# -*- coding: utf-8 -*-
"""
Supervisório de Queimador — porte Python/Streamlit do firmware ESP8266.

Mapeamento do firmware:
    BurnerLogic.h  -> seção "LÓGICA DO QUEIMADOR"  (evaluate, Debouncer, UptimeClock, EventLog)
    TempLogic.h    -> seção "LÓGICA DE TEMPERATURA" (convert, MovingAverage, TrendBuffer, Averager)
    .ino (loop)    -> SimSupervisor (thread de fundo, mesma cadência: ADC 20 ms, entradas 5 ms)
    .ino (JSON)    -> status_dict() / trend_dict()  (mesmo formato de /api/status e /api/trend)
    WebUI.h        -> funções html_* + gráfico Plotly

Fontes de dados:
    1) Simulador   -> controles na barra lateral (entradas, temperatura, falhas, ruído/EMI)
    2) ESP8266 real -> consulta HTTP (Basic Auth) em /api/status e /api/trend

ESCOPO: apenas SUPERVISÃO. Não é camada de segurança e não comanda a válvula de gás.

Requisitos:  pip install "streamlit>=1.37" plotly requests
Execução  :  streamlit run supervisorio_queimador.py
Tema      :  recomendado .streamlit/config.toml  ->  [theme]  base = "dark"
"""
from __future__ import annotations

import math
import random
import threading
import time
from collections import deque
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from typing import Optional

import plotly.graph_objects as go
import requests
import streamlit as st

try:
    from zoneinfo import ZoneInfo
    TZ = ZoneInfo("America/Sao_Paulo")  # ajuste o fuso se necessário
except Exception:  # sem tzdata: usa o horário local do servidor
    TZ = None

# =====================================================================
# LÓGICA DE TEMPERATURA  (TempLogic.h)
# =====================================================================
INVALID = -32768
TEMP_OK, TEMP_LOW, TEMP_HIGH = 0, 1, 2


@dataclass
class TempConfig:
    adc_counts: float = 1023.0       # fundo de escala do ADC (ESP8266: 1023)
    adc_full_scale_v: float = 3.2    # tensão externa que leva o ADC ao fundo de escala
    offset_v: float = 0.0            # correção de zero (V)
    v_at_min: float = 0.0            # tensão em t_min (4 mA)
    v_at_max: float = 3.0            # tensão em t_max (20 mA)
    t_min: float = 0.0
    t_max: float = 400.0
    fault_margin_v: float = 0.05


@dataclass
class Reading:
    status: int = TEMP_OK
    t10: int = INVALID   # décimos de °C
    volts: float = 0.0


def convert(counts: float, c: TempConfig) -> Reading:
    r = Reading()
    r.volts = counts * c.adc_full_scale_v / c.adc_counts + c.offset_v
    saturated = counts >= c.adc_counts - 0.5
    if r.volts < c.v_at_min - c.fault_margin_v:
        r.status = TEMP_LOW
        return r
    if saturated or r.volts > c.v_at_max + c.fault_margin_v:
        r.status = TEMP_HIGH
        return r
    t = c.t_min + (r.volts - c.v_at_min) * (c.t_max - c.t_min) / (c.v_at_max - c.v_at_min)
    t = min(max(t, c.t_min), c.t_max)
    t10 = t * 10.0
    r.t10 = int(t10 + 0.5 if t10 >= 0.0 else t10 - 0.5)  # int() trunca como static_cast
    return r


class MovingAverage:
    """Janela de N leituras com média aparada (descarta maior e menor)."""

    def __init__(self, n: int):
        assert n > 2, "N deve ser maior que 2"
        self.n = n
        self.buf = [0] * n
        self.idx = 0

    def fill(self, v: int):
        self.buf = [v] * self.n
        self.idx = 0

    def add(self, v: int):
        self.buf[self.idx] = v
        self.idx = (self.idx + 1) % self.n

    def trimmed_mean(self) -> float:
        return (sum(self.buf) - min(self.buf) - max(self.buf)) / (self.n - 2)


class TrendBuffer:
    """Buffer circular de tamanho fixo; at(0) = mais antiga."""

    def __init__(self, n: int):
        self.buf = deque(maxlen=n)

    def push(self, v: int):
        self.buf.append(v)

    def clear(self):
        self.buf.clear()

    def as_list(self):
        return list(self.buf)


def _idiv(a: int, b: int) -> int:
    """Divisão inteira truncando para zero (igual ao C++)."""
    q = abs(a) // b
    return q if a >= 0 else -q


class Averager:
    def __init__(self):
        self.sum = 0
        self.n = 0

    def add(self, v: int):
        if v == INVALID:
            return
        self.sum += v
        self.n += 1

    def take(self) -> int:
        out = INVALID
        if self.n > 0:
            half = self.n // 2
            out = _idiv(self.sum + (half if self.sum >= 0 else -half), self.n)
        self.sum = 0
        self.n = 0
        return out


# =====================================================================
# LÓGICA DO QUEIMADOR  (BurnerLogic.h)
# =====================================================================
IN_AIR, IN_GAS_MIN, IN_GAS_MAX, IN_IGNITER, IN_VALVE, IN_FLAME, IN_FAULT = range(7)
IN_COUNT = 7
IN_KEYS = ["air", "gmin", "gmax", "ign", "valve", "flame", "fault"]

BLK_AIR, BLK_GAS_MIN, BLK_GAS_MAX, BLK_VALVE = 1, 2, 4, 8

EV_FLAME_VALID_OFF = IN_COUNT * 2  # 14
EV_FLAME_VALID_ON = 15
EV_MISMATCH_OFF = 16
EV_MISMATCH_ON = 17
EV_BOOT = 18
EV_TEMP_FAULT_ON = 19
EV_TEMP_FAULT_OFF = 20


def event_code(inp: int, state: bool) -> int:
    return inp * 2 + (1 if state else 0)


@dataclass
class BStatus:
    inp: list = field(default_factory=lambda: [False] * IN_COUNT)
    flame_on: bool = False          # chama VALIDADA
    blockers: int = 0
    fault: bool = False
    valve_should_be_closed: bool = False
    valve_mismatch: bool = False
    flame_no_permissive: bool = False
    alarm: bool = False


def evaluate(inp) -> BStatus:
    s = BStatus(inp=list(inp))
    if not inp[IN_AIR]:
        s.blockers |= BLK_AIR
    if not inp[IN_GAS_MIN]:
        s.blockers |= BLK_GAS_MIN
    if not inp[IN_GAS_MAX]:
        s.blockers |= BLK_GAS_MAX
    if not inp[IN_VALVE]:
        s.blockers |= BLK_VALVE
    s.fault = bool(inp[IN_FAULT])
    s.flame_on = bool(inp[IN_FLAME]) and s.blockers == 0 and not s.fault
    s.flame_no_permissive = bool(inp[IN_FLAME]) and s.blockers != 0
    s.valve_should_be_closed = s.fault
    s.valve_mismatch = s.fault and bool(inp[IN_VALVE])
    s.alarm = s.fault or s.valve_mismatch or s.flame_no_permissive
    return s


class Debouncer:
    """A saída só muda após hold_ms com a leitura constante."""

    def __init__(self):
        self.hold_ms = 50
        self.stable = False
        self.candidate = False
        self.since = 0

    def begin(self, hold_ms: int, initial: bool, now_ms: int):
        self.hold_ms = hold_ms
        self.stable = self.candidate = initial
        self.since = now_ms

    def update(self, raw: bool, now_ms: int) -> bool:
        if raw != self.candidate:
            self.candidate = raw
            self.since = now_ms
        elif self.candidate != self.stable and ((now_ms - self.since) & 0xFFFFFFFF) >= self.hold_ms:
            self.stable = self.candidate
        return self.stable

    def value(self) -> bool:
        return self.stable


class UptimeClock:
    """Uptime monotônico em segundos, imune ao overflow de 32 bits do millis()."""

    def __init__(self):
        self.last = 0
        self.sec = 0
        self.rem_ms = 0

    def begin(self, now_ms: int):
        self.last = now_ms
        self.sec = now_ms // 1000
        self.rem_ms = now_ms % 1000

    def update(self, now_ms: int):
        delta = (now_ms - self.last) & 0xFFFFFFFF
        self.last = now_ms
        self.sec += delta // 1000
        self.rem_ms += delta % 1000
        if self.rem_ms >= 1000:
            self.rem_ms -= 1000
            self.sec += 1

    def seconds(self) -> int:
        return self.sec


class EventLog:
    def __init__(self, n: int):
        self.buf = deque(maxlen=n)

    def push(self, uptime_s: int, code: int):
        self.buf.append((uptime_s, code))

    def newest_first(self):
        return list(reversed(self.buf))


def record_changes(prev: BStatus, cur: BStatus, now_s: int, log: EventLog):
    for i in range(IN_COUNT):
        if prev.inp[i] != cur.inp[i]:
            log.push(now_s, event_code(i, cur.inp[i]))
    if prev.flame_on != cur.flame_on:
        log.push(now_s, EV_FLAME_VALID_ON if cur.flame_on else EV_FLAME_VALID_OFF)
    if prev.valve_mismatch != cur.valve_mismatch:
        log.push(now_s, EV_MISMATCH_ON if cur.valve_mismatch else EV_MISMATCH_OFF)


# =====================================================================
# PARÂMETROS (iguais ao .ino)
# =====================================================================
INPUT_DEBOUNCE_MS = [100, 100, 100, 50, 50, 50, 50]  # ordem do enum InputId
ADC_PERIOD_MS = 20
POLL_PERIOD_MS = 5
TEMP_FAULT_HOLD_MS = 2000
EVENT_LOG_SIZE = 30
TREND_FAST_PERIOD_S = 10
TREND_FAST_N = 360                      # 1 h
TREND_SLOW_EVERY = 30
TREND_SLOW_PERIOD_S = TREND_FAST_PERIOD_S * TREND_SLOW_EVERY  # 300 s
TREND_SLOW_N = 288                      # 24 h
WIN_S = [3600, 86400]
POLL_TREND_S = [10, 60]

SCEN_NORMAL = "Normal"
SCEN_SAT = "Sensor rompido (saturação do ADC)"
SCEN_OPEN = "Laço aberto (0 mA)"

CFG_0_3V = TempConfig(v_at_min=0.0, v_at_max=3.0)
CFG_SHUNT = TempConfig(v_at_min=0.6, v_at_max=3.0)   # shunt 150 ohm: 4 mA = 0,6 V


# =====================================================================
# SIMULADOR (equivale ao loop() do firmware, em thread de fundo)
# =====================================================================
@dataclass
class SimIO:
    inputs: list = field(default_factory=lambda: [True, True, True, False, False, False, False])
    temp_sp: float = 180.0
    scenario: str = SCEN_NORMAL
    noise: bool = False


class SimSupervisor:
    rotulo = "Simulador"

    def __init__(self, cfg: TempConfig):
        self.lock = threading.RLock()
        self.cfg = cfg
        self.io = SimIO()
        self._rng = random.Random()
        self._t0 = time.monotonic()
        self._stop = threading.Event()
        self._thread: Optional[threading.Thread] = None

        now = self._now_ms()
        self.deb = [Debouncer() for _ in range(IN_COUNT)]
        for i in range(IN_COUNT):
            self.deb[i].begin(INPUT_DEBOUNCE_MS[i], self.io.inputs[i], now)
        self.uptime = UptimeClock()
        self.uptime.begin(now)

        self.t_proc = self.io.temp_sp
        self.adc_window = MovingAverage(16)
        self.adc_window.fill(self._adc_read(0.0))
        for _ in range(15):
            self.adc_window.add(self._adc_read(0.0))
        self.adc_mean = self.adc_window.trimmed_mean()
        self.temp_now = convert(self.adc_mean, self.cfg)
        self.temp_fault_deb = Debouncer()
        self.temp_fault_deb.begin(TEMP_FAULT_HOLD_MS, self.temp_now.status != TEMP_OK, now)
        self.temp_fault_dir = self.temp_now.status if self.temp_now.status != TEMP_OK else 0

        self.trend_fast = TrendBuffer(TREND_FAST_N)
        self.trend_slow = TrendBuffer(TREND_SLOW_N)
        self.slow_acc = Averager()
        self.slow_count = 0
        self.last_fast_s = self.last_slow_s = self.uptime.seconds()

        self.events = EventLog(EVENT_LOG_SIZE)
        self.status = evaluate(list(self.io.inputs))
        self.events.push(self.uptime.seconds(), EV_BOOT)

    # ---------- tempo ----------
    def _now_ms(self) -> int:
        return int((time.monotonic() - self._t0) * 1000) & 0xFFFFFFFF

    # ---------- controle externo (UI) ----------
    def set_inputs(self, vals):
        with self.lock:
            self.io.inputs = [bool(v) for v in vals]

    def set_process(self, temp_sp: float, scenario: str, noise: bool):
        with self.lock:
            self.io.temp_sp = float(temp_sp)
            self.io.scenario = scenario
            self.io.noise = bool(noise)

    def set_config(self, cfg: TempConfig):
        with self.lock:
            self.cfg = cfg

    def fill_demo_history(self):
        """Preenche os históricos com uma curva sintética (para testar o gráfico)."""
        with self.lock:
            self.trend_fast.clear()
            self.trend_slow.clear()
            for i in range(TREND_FAST_N):
                v = INVALID if i in (120, 121, 122, 300) else int((180 + 40 * math.sin(i / 28) + self._rng.gauss(0, 2)) * 10)
                self.trend_fast.push(v)
            for i in range(TREND_SLOW_N):
                self.trend_slow.push(int((180 + 50 * math.sin(i / 40) + self._rng.gauss(0, 3)) * 10))
            self.slow_acc = Averager()
            self.slow_count = 0
            self.last_fast_s = self.last_slow_s = self.uptime.seconds()

    # ---------- "hardware" simulado ----------
    def _adc_read(self, dt_s: float) -> int:
        io, c = self.io, self.cfg
        if dt_s > 0:  # processo com atraso de 1ª ordem (tau = 5 s)
            self.t_proc += (io.temp_sp - self.t_proc) * min(dt_s / 5.0, 1.0)
        if io.scenario == SCEN_SAT:
            return 1023
        if io.scenario == SCEN_OPEN:
            v = 0.0
        else:
            v = c.v_at_min + (self.t_proc - c.t_min) * (c.v_at_max - c.v_at_min) / (c.t_max - c.t_min)
        counts = (v - c.offset_v) * c.adc_counts / c.adc_full_scale_v
        if io.noise:
            counts += self._rng.gauss(0, 1.5)
            if self._rng.random() < 0.01:   # pico de EMI (ex.: trafo de ignição)
                counts += 200
        return int(min(max(round(counts), 0), 1023))

    # ---------- passos do loop() ----------
    def _sample_temperature(self, now_ms: int, dt_s: float):
        self.adc_window.add(self._adc_read(dt_s))
        self.adc_mean = self.adc_window.trimmed_mean()
        self.temp_now = convert(self.adc_mean, self.cfg)
        if self.temp_now.status != TEMP_OK:
            self.temp_fault_dir = self.temp_now.status
        was = self.temp_fault_deb.value()
        is_ = self.temp_fault_deb.update(self.temp_now.status != TEMP_OK, now_ms)
        if is_ != was:
            self.events.push(self.uptime.seconds(), EV_TEMP_FAULT_ON if is_ else EV_TEMP_FAULT_OFF)

    def _trend_tick(self):
        s = self.uptime.seconds()
        if s - self.last_fast_s < TREND_FAST_PERIOD_S:
            return
        self.last_fast_s = s
        self.trend_fast.push(self.temp_now.t10)
        self.slow_acc.add(self.temp_now.t10)
        self.slow_count += 1
        if self.slow_count >= TREND_SLOW_EVERY:
            self.slow_count = 0
            self.trend_slow.push(self.slow_acc.take())
            self.last_slow_s = s

    def _poll_inputs(self, now_ms: int):
        raw = self.io.inputs
        inp = [self.deb[i].update(raw[i], now_ms) for i in range(IN_COUNT)]
        nxt = evaluate(inp)
        record_changes(self.status, nxt, self.uptime.seconds(), self.events)
        self.status = nxt

    def _loop(self):
        last_adc = last_poll = self._now_ms()
        while not self._stop.is_set():
            with self.lock:
                now = self._now_ms()
                self.uptime.update(now)
                if now - last_adc >= ADC_PERIOD_MS:
                    self._sample_temperature(now, (now - last_adc) / 1000.0)
                    last_adc = now
                self._trend_tick()
                if now - last_poll >= POLL_PERIOD_MS:
                    last_poll = now
                    self._poll_inputs(now)
            time.sleep(0.005)

    def start(self):
        if self._thread and self._thread.is_alive():
            return
        self._stop.clear()
        self._thread = threading.Thread(target=self._loop, daemon=True, name="sim-queimador")
        self._thread.start()

    def stop(self):
        self._stop.set()

    # ---------- API (mesmo formato do JSON do firmware) ----------
    def status_dict(self) -> dict:
        with self.lock:
            s, t = self.status, self.temp_now
            return {
                "up": self.uptime.seconds(),
                "in": {k: int(s.inp[i]) for i, k in enumerate(IN_KEYS)},
                "flame": int(s.flame_on), "blk": s.blockers, "fault": int(s.fault),
                "mismatch": int(s.valve_mismatch), "noPerm": int(s.flame_no_permissive),
                "alarm": int(s.alarm),
                "t10": None if t.t10 == INVALID else t.t10,
                "tst": self.temp_fault_dir if self.temp_fault_deb.value() else 0,
                "mv": int(t.volts * 1000.0), "adc": int(self.adc_mean + 0.5),
                "rssi": 0, "heap": None,
                "ev": [[u, c] for u, c in self.events.newest_first()],
            }

    def trend_dict(self, rng: int) -> dict:
        with self.lock:
            now = self.uptime.seconds()
            if rng == 1:
                buf, iv, age = self.trend_slow, TREND_SLOW_PERIOD_S, now - self.last_slow_s
            else:
                buf, iv, age = self.trend_fast, TREND_FAST_PERIOD_S, now - self.last_fast_s
            return {"iv": iv, "age": age, "at": time.time(),
                    "v": [None if v == INVALID else v for v in buf.as_list()]}

    def status(self_) -> tuple:  # noqa: D401  (interface comum com EspBackend)
        raise NotImplementedError


# interface comum: status() -> (dict|None, stale)
def _sim_status(self) -> tuple:
    return self.status_dict(), False


SimSupervisor.status = _sim_status  # type: ignore[assignment]
SimSupervisor.trend = lambda self, rng: self.trend_dict(rng)  # type: ignore[attr-defined]


# =====================================================================
# BACKEND ESP8266 REAL (HTTP)
# =====================================================================
class EspBackend:
    rotulo = "ESP8266"

    def __init__(self, base_url: str, user: str, password: str):
        self.base = base_url.rstrip("/")
        self.auth = (user, password)
        self.fails = 0
        self.last: Optional[dict] = None

    def _get(self, path: str, timeout: float):
        r = requests.get(self.base + path, auth=self.auth, timeout=timeout,
                         headers={"Cache-Control": "no-store"})
        r.raise_for_status()
        return r.json()

    def status(self) -> tuple:
        try:
            self.last = self._get("/api/status", 2.0)
            self.fails = 0
        except Exception:
            self.fails += 1
        return self.last, self.fails >= 3

    def trend(self, rng: int) -> Optional[dict]:
        try:
            j = self._get(f"/api/trend?r={rng}", 5.0)
            j["at"] = time.time()
            return j
        except Exception:
            return None


# =====================================================================
# TEXTOS DA INTERFACE (WebUI.h)
# =====================================================================
IN_UI = [  # (chave, tag, nome, [txt0, txt1], [cls0, cls1])
    ("air", "PSL-201", "Pressostato de ar", ["FALHA", "OK"], ["bad", "ok"]),
    ("gmin", "PSL-101", "Pressostato gás mínima", ["FALHA", "OK"], ["bad", "ok"]),
    ("gmax", "PSH-102", "Pressostato gás máxima", ["FALHA", "OK"], ["bad", "ok"]),
    ("ign", "TR-301", "Trafo de ignição", ["DESLIGADO", "LIGADO"], ["neu", "act"]),
    ("valve", "XV-101", "Válvula solenoide", ["FECHADA", "ABERTA"], ["neu", "ok"]),
    ("flame", "BE-401", "Chama", ["APAGADA", "ACESA"], ["neu", "act"]),
    ("fault", "BC-401", "Controlador de chama", ["NORMAL", "FALHA"], ["ok", "bad"]),
]
BLOCKER_NAMES = ["Pressostato de ar", "Pressostato gás mínima",
                 "Pressostato gás máxima", "Válvula solenoide fechada"]
EV_UI = [
    ("Pressostato de ar → FALHA", "bad"), ("Pressostato de ar → OK", "ok"),
    ("Pressostato gás mínima → FALHA", "bad"), ("Pressostato gás mínima → OK", "ok"),
    ("Pressostato gás máxima → FALHA", "bad"), ("Pressostato gás máxima → OK", "ok"),
    ("Trafo de ignição → DESLIGADO", "neu"), ("Trafo de ignição → LIGADO", "act"),
    ("Válvula solenoide → FECHADA", "neu"), ("Válvula solenoide → ABERTA", "ok"),
    ("Sensor de chama → sem sinal", "neu"), ("Sensor de chama → sinal presente", "act"),
    ("Controlador de chama → falha normalizada", "ok"), ("Controlador de chama → FALHA", "bad"),
    ("Chama → APAGADA", "neu"), ("Chama → ACESA", "act"),
    ("Discrepância de válvula normalizada", "ok"),
    ("DISCREPÂNCIA: falha ativa com válvula ABERTA", "bad"),
    ("Supervisório iniciado", "neu"),
    ("Sinal de temperatura → FORA DA FAIXA", "bad"), ("Sinal de temperatura → normalizado", "ok"),
]

CSS = """
<style>
.stApp{background:#23272b}
.block-container{max-width:1100px;padding-top:1rem}
.hmi{--bg:#23272b;--pn:#2f343a;--ln:#454c54;--tx:#e8eaec;--mu:#98a2ab;--ok:#3fae5a;--bad:#e5384a;--act:#f2a33a;--neu:#7b858e;--tr:#4db6e6;
 color:var(--tx);font:14px/1.4 "Segoe UI",Roboto,"Helvetica Neue",Arial,sans-serif}
.hmi *{box-sizing:border-box}
.hmi .hd{display:flex;justify-content:space-between;align-items:center;gap:8px;flex-wrap:wrap;padding:10px 16px;background:#1a1d20;border:1px solid var(--ln);border-bottom:2px solid var(--ln);border-radius:4px}
.hmi .hd b{font-size:17px}
.hmi .hd small{display:block;color:var(--mu);font-size:12px}
.hmi .hr{display:flex;gap:12px;align-items:center;color:var(--mu);font-size:12px}
.hmi .badge{padding:3px 10px;border-radius:3px;font-weight:700;font-size:12px;background:var(--neu);color:#111}
.hmi .badge.ok{background:var(--ok)}
.hmi .badge.bad{background:var(--bad);color:#fff}
.hmi .card{background:var(--pn);border:1px solid var(--ln);border-radius:4px;padding:12px 14px}
.hmi .lbl{font-size:12px;color:var(--mu);font-weight:600;margin-bottom:8px}
.hmi .alarms{display:grid;gap:6px}
.hmi .al{background:var(--bad);color:#fff;font-weight:700;padding:10px 14px;border-radius:3px;animation:bl 1s steps(2,start) infinite}
.hmi .al.w{background:#b9770e;animation:none}
@keyframes bl{to{background:#8f1f2b}}
@media (prefers-reduced-motion:reduce){.hmi .al{animation:none}}
.hmi .ok{--c:var(--ok)}.hmi .bad{--c:var(--bad)}.hmi .neu{--c:var(--neu)}.hmi .act{--c:var(--act)}.hmi .tr{--c:var(--tr)}
.hmi .flame{display:flex;align-items:center;gap:18px;flex-wrap:wrap}
.hmi .bigv{font-size:34px;font-weight:700;padding:6px 20px;border-radius:3px;border:2px solid var(--c,var(--neu));color:var(--c,var(--neu));display:inline-block}
.hmi .chip{display:inline-block;margin:3px 6px 0 0;padding:3px 10px;border-radius:3px;font-size:12px;font-weight:600;border:1px solid var(--c,var(--neu));color:var(--c,var(--neu))}
.hmi .tiles{display:grid;grid-template-columns:repeat(auto-fill,minmax(210px,1fr));gap:10px}
.hmi .tile{background:var(--pn);border:1px solid var(--ln);border-left:6px solid var(--c,var(--neu));border-radius:4px;padding:10px 12px}
.hmi .tg{font:11px/1 ui-monospace,Consolas,monospace;color:var(--mu)}
.hmi .nm{font-weight:600;margin:5px 0 3px}
.hmi .vl{font-size:20px;font-weight:700;color:var(--c,var(--neu))}
.hmi .sb{font-size:11px;color:var(--mu);min-height:15px}
.hmi.stale .vl,.hmi.stale .bigv,.hmi.stale svg{opacity:.3}
.hmi svg.diag{width:100%;height:auto;display:block}
.hmi .pipe line{stroke:#6c767f;stroke-width:4}
.hmi .sig{stroke:var(--neu);stroke-dasharray:4 4;stroke-width:1.5}
.hmi .eq rect,.hmi .eq path{fill:var(--bg);stroke:var(--c,var(--neu));stroke-width:2}
.hmi .eq line{stroke:var(--c,var(--neu));stroke-width:2}
.hmi .eq text{fill:var(--c,var(--neu));font:600 11px "Segoe UI",Arial,sans-serif;text-anchor:middle}
.hmi #m-flame .fi{fill:none;stroke-width:1.5}
.hmi #m-flame.act .fo{fill:var(--act)}
.hmi #m-flame.act .fi{fill:#ffd27a;stroke:none}
.hmi .cap{fill:var(--mu);font:11px "Segoe UI",Arial,sans-serif}
.hmi .trh{display:flex;align-items:center;gap:16px;flex-wrap:wrap;margin-bottom:6px}
.hmi .trh .bigv{font-size:30px;min-width:170px;text-align:center}
.hmi .tstats{display:flex;gap:20px;flex-wrap:wrap;margin-top:4px;color:var(--mu);font-size:12px}
.hmi .tstats b{color:var(--tx);font-weight:600}
.hmi .evw{max-height:380px;overflow-y:auto}
.hmi table{width:100%;border-collapse:collapse;font-size:12px}
.hmi td{padding:4px 6px;border-top:1px solid var(--ln)}
.hmi td:first-child{color:var(--mu);white-space:nowrap}
.hmi td+td{color:var(--c,var(--tx))}
.hmi .ft{display:flex;gap:18px;flex-wrap:wrap;padding:8px 16px;background:#1a1d20;border:1px solid var(--ln);border-radius:4px;color:var(--mu);font-size:12px}
</style>
"""


# =====================================================================
# HELPERS DE FORMATAÇÃO
# =====================================================================
def f_temp(v10) -> str:
    return "--" if v10 is None else f"{v10 / 10:.1f}".replace(".", ",") + " °C"


def hms(s: int) -> str:
    return f"{s // 3600}h {s % 3600 // 60:02d}m {s % 60:02d}s"


def agora() -> datetime:
    return datetime.now(TZ) if TZ else datetime.now()


def ts_para_dt(ts: float) -> datetime:
    return datetime.fromtimestamp(ts, TZ) if TZ else datetime.fromtimestamp(ts)


def mostrar_plot(fig, key):
    try:
        st.plotly_chart(fig, width="stretch", key=key, config={"displayModeBar": False})
    except TypeError:
        st.plotly_chart(fig, use_container_width=True, key=key, config={"displayModeBar": False})


# =====================================================================
# LÓGICA DE APRESENTAÇÃO (equivale a render(d) do JavaScript)
# =====================================================================
def classes_tiles(d: dict) -> dict:
    out = {}
    for k, tag, nome, txt, cls in IN_UI:
        v = 1 if (d["flame"] if k == "flame" else d["in"][k]) else 0
        c, sub = cls[v], ""
        if k == "valve" and d["fault"]:
            sub = ("ATENÇÃO: falha ativa e retorno indica ABERTA" if d["mismatch"]
                   else "Falha ativa: esperado FECHADA")
            if d["mismatch"]:
                c = "bad"
        if k == "flame":
            sub = "Sensor: " + ("sinal presente" if d["in"]["flame"] else "sem sinal")
            if d["noPerm"]:
                c = "bad"
                sub += " · sem permissivos"
        out[k] = (c, txt[v], sub, tag, nome)
    out["_fault_diag"] = ("bad" if d["fault"] else "ok",)
    return out


def html_header(stale: bool) -> str:
    comm = ('<span class="badge bad">SEM COMUNICAÇÃO</span>' if stale
            else '<span class="badge ok">ONLINE</span>')
    return (f'<div class="hmi{" stale" if stale else ""}"><div class="hd"><div>'
            '<b>Supervisório queimador a gás industrial SDB</b><small>BRN-01 · linha de gás</small></div>'
            f'<div class="hr"><span>{agora():%d/%m/%Y %H:%M:%S}</span>{comm}</div></div></div>')


def html_alarmes(d: dict, stale: bool) -> str:
    if stale:
        a = ('<div class="al">SEM COMUNICAÇÃO COM O SUPERVISÓRIO · '
             'dados exibidos estão desatualizados</div>')
    else:
        a = ""
        if d["fault"]:
            a += '<div class="al">FALHA NO QUEIMADOR · controlador de chama em falha · a válvula solenoide deve estar FECHADA</div>'
        if d["mismatch"]:
            a += '<div class="al">DISCREPÂNCIA · falha ativa, mas o retorno da válvula indica ABERTA · executar parada de emergência e verificar em campo</div>'
        if d["noPerm"]:
            a += '<div class="al">Sinal de chama presente com permissivos fora · verificar sensor de chama</div>'
        if d["tst"]:
            motivo = ("ABAIXO do mínimo (laço aberto ou sem sinal)" if d["tst"] == 1
                      else "ACIMA do máximo (sensor rompido ou saturação)")
            a += (f'<div class="al w">Sinal de temperatura {motivo} · '
                  'verificar transmissor, cabo e alimentação do laço</div>')
    return f'<div class="hmi stale-off"><div class="alarms">{a}</div></div>' if a else ""


def html_chama(d: dict, stale: bool) -> str:
    cls = "act" if d["flame"] else ("bad" if d["fault"] else "neu")
    txt = "ACESA" if d["flame"] else "APAGADA"
    if d["flame"]:
        why = '<span class="chip ok">Todas as condições atendidas</span>'
    else:
        chips = "".join(f'<span class="chip bad">{n}</span>'
                        for i, n in enumerate(BLOCKER_NAMES) if d["blk"] & (1 << i))
        if d["fault"]:
            chips += '<span class="chip bad">Falha do controlador de chama</span>'
        why = ('<div class="sb">Condições não atendidas:</div>' + chips if chips else
               '<span class="chip neu">Sem sinal de chama · condições de processo atendidas</span>')
    return (f'<div class="hmi{" stale" if stale else ""}"><div class="card"><div class="lbl">Estado da chama</div>'
            f'<div class="flame"><div class="bigv {cls}">{txt}</div><div>{why}</div></div></div></div>')


def html_tiles(cl: dict, stale: bool) -> str:
    t = ""
    for k, *_ in IN_UI:
        c, txt, sub, tag, nome = cl[k]
        t += (f'<div class="tile {c}"><div class="tg">{tag}</div><div class="nm">{nome}</div>'
              f'<div class="vl">{txt}</div><div class="sb">{sub}</div></div>')
    return f'<div class="hmi{" stale" if stale else ""}"><div class="tiles">{t}</div></div>'


def html_temp_topo(d: dict, stale: bool) -> str:
    ok = d["t10"] is not None and not d["tst"]
    val = f_temp(d["t10"]) if ok else "-- °C"
    chip = ('<span class="chip bad">Sinal fora da faixa</span>' if d["tst"]
            else '<span class="chip ok">Sinal OK</span>')
    sub = f'Sinal: {d["mv"] / 1000:.2f} V · ADC {d["adc"]}'.replace(".", ",", 1)
    return (f'<div class="hmi{" stale" if stale else ""}"><div class="lbl">Temperatura do processo · TT-501 (PT100, 0 a 400 °C)</div>'
            f'<div class="trh"><div class="bigv {"tr" if ok else "bad"}">{val}</div>'
            f'<div>{chip}<div class="sb">{sub}</div></div></div></div>')


def svg_diagrama(cl: dict) -> str:
    c = {k: cl[k][0] for k, *_ in IN_UI}
    fault_c = cl["_fault_diag"][0]
    return (
        '<svg class="diag" viewBox="0 0 760 270" role="img" aria-label="Diagrama do queimador">'
        '<g class="pipe"><line x1="10" y1="100" x2="570" y2="100"/><line x1="10" y1="200" x2="610" y2="200"/><line x1="610" y1="200" x2="610" y2="130"/></g>'
        '<text class="cap" x="12" y="88">Gás</text><text class="cap" x="12" y="190">Ar</text>'
        f'<g id="m-gmin" class="eq {c["gmin"]}"><rect x="110" y="56" width="80" height="26"/><line x1="150" y1="82" x2="150" y2="100"/><text x="150" y="73">PSL-101</text></g>'
        '<text class="cap" x="150" y="122" text-anchor="middle">Gás mínima</text>'
        f'<g id="m-valve" class="eq {c["valve"]}"><path d="M270 86L295 100L270 114Z M320 86L295 100L320 114Z"/><rect x="283" y="52" width="24" height="16"/><line x1="295" y1="68" x2="295" y2="100"/><text x="295" y="44">XV-101</text></g>'
        '<text class="cap" x="295" y="132" text-anchor="middle">Solenoide</text>'
        f'<g id="m-gmax" class="eq {c["gmax"]}"><rect x="400" y="56" width="80" height="26"/><line x1="440" y1="82" x2="440" y2="100"/><text x="440" y="73">PSH-102</text></g>'
        '<text class="cap" x="440" y="122" text-anchor="middle">Gás máxima</text>'
        f'<g id="m-air" class="eq {c["air"]}"><rect x="260" y="156" width="80" height="26"/><line x1="300" y1="182" x2="300" y2="200"/><text x="300" y="173">PSL-201</text></g>'
        '<text class="cap" x="300" y="222" text-anchor="middle">Ar de combustão</text>'
        f'<g id="m-ign" class="eq {c["ign"]}"><rect x="550" y="8" width="120" height="26"/><line x1="610" y1="34" x2="610" y2="70"/><text x="610" y="25">TR-301 ignição</text></g>'
        '<g class="eq neu"><rect x="570" y="70" width="80" height="60"/><text x="610" y="104">Queimador</text></g>'
        f'<g id="m-flame" class="eq {c["flame"]}" transform="translate(668,70)">'
        '<path class="fo" d="M20 0C22 14 36 22 36 40C36 52 28 60 20 60C12 60 4 52 4 40C4 30 10 24 12 16C15 22 16 26 18 28C20 20 18 10 20 0Z"/>'
        '<path class="fi" d="M20 28C22 36 28 40 28 47C28 54 24 58 20 58C16 58 12 54 12 47C12 41 18 36 20 28Z"/>'
        '<text x="20" y="76">BE-401 chama</text></g>'
        '<line class="sig" x1="660" y1="190" x2="640" y2="130"/>'
        f'<g id="m-fault" class="eq {fault_c}"><rect x="650" y="190" width="100" height="60"/><text x="700" y="216">Controlador</text><text x="700" y="232">de chama</text></g>'
        '</svg>')


def html_diagrama(cl: dict, stale: bool) -> str:
    return (f'<div class="hmi{" stale" if stale else ""}"><div class="card"><div class="lbl">Diagrama do queimador</div>'
            f'{svg_diagrama(cl)}</div></div>')


def html_eventos(d: dict) -> str:
    linhas = ""
    ref = agora()
    for t, code in d["ev"]:
        txt, cls = EV_UI[code] if 0 <= code < len(EV_UI) else (f"Evento {code}", "neu")
        quando = (ref - timedelta(seconds=max(d["up"] - t, 0))).strftime("%d/%m/%Y %H:%M:%S")
        linhas += f'<tr class="{cls}"><td>{quando}</td><td>{txt}</td></tr>'
    return ('<div class="hmi"><div class="card"><div class="lbl">Registro de eventos (últimos 30)</div>'
            f'<div class="evw"><table>{linhas}</table></div></div></div>')


def html_rodape(d: dict, rotulo: str) -> str:
    wifi = f'{d["rssi"]} dBm' if d.get("rssi") else "AP local"
    heap = f'{d["heap"] / 1024:.1f} kB' if d.get("heap") else "n/d"
    return (f'<div class="hmi"><div class="ft"><span>Uptime: {hms(int(d["up"]))}</span>'
            f'<span>Wi-Fi: {wifi}</span><span>Heap livre: {heap}</span><span>Fonte: {rotulo}</span></div></div>')


# =====================================================================
# GRÁFICO DE TENDÊNCIA (equivale ao <canvas> do WebUI)
# =====================================================================
def grafico_tendencia(tr: Optional[dict], rng: int) -> tuple:
    W = WIN_S[rng]
    agora_ts = time.time()
    xs, ys = [], []
    if tr and tr["v"]:
        t_new = tr["at"] - tr["age"]
        n = len(tr["v"])
        for i, v in enumerate(tr["v"]):
            xs.append(ts_para_dt(t_new - (n - 1 - i) * tr["iv"]))
            ys.append(None if v is None else v / 10.0)
    validos = [y for y in ys if y is not None]

    lo, hi = 0.0, 400.0
    if validos:
        lo, hi = min(validos) - 5, max(validos) + 5
        if hi - lo < 40:
            m = (hi + lo) / 2
            lo, hi = m - 20, m + 20

    isolados_x, isolados_y = [], []
    for i, y in enumerate(ys):
        if y is None:
            continue
        ant = ys[i - 1] if i > 0 else None
        prox = ys[i + 1] if i < len(ys) - 1 else None
        if ant is None and prox is None:
            isolados_x.append(xs[i])
            isolados_y.append(y)

    fig = go.Figure()
    fig.add_scatter(x=xs, y=ys, mode="lines", connectgaps=False, name="Temperatura",
                    line=dict(color="#4db6e6", width=2),
                    hovertemplate="%{y:.1f} °C<br>%{x|%d/%m/%Y %H:%M:%S}<extra></extra>")
    if isolados_x:
        fig.add_scatter(x=isolados_x, y=isolados_y, mode="markers", showlegend=False,
                        marker=dict(color="#4db6e6", size=6), hoverinfo="skip")
    fig.update_layout(
        height=260, margin=dict(t=10, b=10, l=10, r=12), showlegend=False,
        paper_bgcolor="rgba(0,0,0,0)", plot_bgcolor="rgba(0,0,0,0)",
        font=dict(color="#98a2ab", size=11), separators=",.", hovermode="x",
        xaxis=dict(range=[ts_para_dt(agora_ts - W), ts_para_dt(agora_ts)], gridcolor="#454c54",
                   tickformat="%H:%M" if rng == 0 else "%d/%m %H:%M", fixedrange=True),
        yaxis=dict(range=[lo, hi], gridcolor="#454c54", ticksuffix=" °C", fixedrange=True),
    )
    if not tr:
        fig.add_annotation(text="Carregando histórico…", showarrow=False, x=0.5, y=0.5,
                           xref="paper", yref="paper")
    elif not validos:
        fig.add_annotation(text="Sem dados válidos nesta janela", showarrow=False, x=0.5, y=0.5,
                           xref="paper", yref="paper")

    if validos:
        vmin, vmax = min(validos), max(validos)
        media = sum(validos) / len(validos)
        stats = (f'<span>Mín: <b>{f_temp(round(vmin * 10))}</b></span>'
                 f'<span>Média: <b>{f_temp(math.floor(media * 10 + 0.5))}</b></span>'
                 f'<span>Máx: <b>{f_temp(round(vmax * 10))}</b></span>')
    else:
        stats = '<span>Mín: <b>--</b></span><span>Média: <b>--</b></span><span>Máx: <b>--</b></span>'
    if tr:
        iv = tr["iv"]
        stats += f'<span>1 ponto a cada {iv // 60} min</span>' if iv >= 60 else f'<span>1 ponto a cada {iv} s</span>'
    return fig, f'<div class="hmi"><div class="tstats">{stats}</div></div>'


def obter_tendencia(backend, rng: int) -> Optional[dict]:
    if isinstance(backend, SimSupervisor):
        return backend.trend_dict(rng)
    cache = st.session_state.setdefault("trend_cache", {})
    ts, data = cache.get(rng, (0.0, None))
    if data is None or time.time() - ts >= POLL_TREND_S[rng]:
        novo = backend.trend(rng)
        cache[rng] = (time.time(), novo or data)
        data = novo or data
    return data


# =====================================================================
# PAINEL (atualiza sozinho a cada 1 s, sem recarregar a página)
# =====================================================================
@st.fragment(run_every=1)
def painel(backend):
    d, stale = backend.status()
    if d is None:
        st.markdown(html_header(True), unsafe_allow_html=True)
        st.error("Sem dados do ESP8266. Verifique URL, usuário/senha e se o computador está "
                 "conectado ao Wi-Fi do equipamento (padrão: QUEIMADOR-HMI).")
        return

    cl = classes_tiles(d)
    st.markdown(html_header(stale), unsafe_allow_html=True)
    alarmes = html_alarmes(d, stale)
    if alarmes:
        st.markdown(alarmes, unsafe_allow_html=True)
    st.markdown(html_chama(d, stale), unsafe_allow_html=True)
    st.markdown(html_tiles(cl, stale), unsafe_allow_html=True)

    with st.container(border=True):
        st.markdown(html_temp_topo(d, stale), unsafe_allow_html=True)
        escolha = st.radio("Janela", ["1 h", "24 h"], horizontal=True,
                           key="trend_rng", label_visibility="collapsed")
        rng = 0 if escolha == "1 h" else 1
        fig, stats_html = grafico_tendencia(obter_tendencia(backend, rng), rng)
        mostrar_plot(fig, key="grafico_temp")
        st.markdown(stats_html, unsafe_allow_html=True)

    st.markdown(html_diagrama(cl, stale), unsafe_allow_html=True)
    st.markdown(html_eventos(d), unsafe_allow_html=True)
    st.markdown(html_rodape(d, backend.rotulo), unsafe_allow_html=True)


# =====================================================================
# BARRA LATERAL / CONTROLES
# =====================================================================
PRESETS = {
    "Em repouso (parado)": dict(air=True, gmin=True, gmax=True, ign=False, valve=False, flame=False, fault=False),
    "Partida: ignição ligada": dict(air=True, gmin=True, gmax=True, ign=True, valve=True, flame=False, fault=False),
    "Operação normal (chama acesa)": dict(air=True, gmin=True, gmax=True, ign=False, valve=True, flame=True, fault=False),
    "Falta de ar de combustão": dict(air=False, gmin=True, gmax=True, ign=False, valve=False, flame=False, fault=True),
    "Chama sem permissivos": dict(air=True, gmin=False, gmax=True, ign=False, valve=True, flame=True, fault=False),
    "Discrepância de válvula": dict(air=True, gmin=True, gmax=True, ign=False, valve=True, flame=False, fault=True),
}
SIM_LABELS = [
    ("air", "Pressostato de ar OK (PSL-201)"),
    ("gmin", "Gás mínima OK (PSL-101)"),
    ("gmax", "Gás máxima OK (PSH-102)"),
    ("ign", "Trafo de ignição LIGADO (TR-301)"),
    ("valve", "Válvula ABERTA (XV-101)"),
    ("flame", "Sinal de chama presente (BE-401)"),
    ("fault", "FALHA no controlador de chama (BC-401)"),
]


def _aplicar_preset():
    for k, v in PRESETS[st.session_state["sim_preset"]].items():
        st.session_state[f"sim_{k}"] = v


def _secret(chave: str, padrao: str) -> str:
    try:
        return str(st.secrets.get(chave, padrao))
    except Exception:
        return padrao


@st.cache_resource
def obter_simulador() -> SimSupervisor:
    sim = SimSupervisor(CFG_0_3V)
    sim.start()
    return sim


def barra_lateral():
    sb = st.sidebar
    sb.title("⚙️ Supervisório")
    sb.caption("Somente supervisão. Não substitui o BMS / controlador de chama nem os intertravamentos.")
    fonte = sb.radio("Fonte de dados", ["Simulador", "ESP8266 real (HTTP)"])

    if fonte.startswith("ESP"):
        url = sb.text_input("URL do ESP8266", _secret("ESP_URL", "http://192.168.4.1"))
        user = sb.text_input("Usuário", _secret("ESP_USER", "operador"))
        pwd = sb.text_input("Senha", _secret("ESP_PASS", ""), type="password")
        assinatura = (url, user, pwd)
        if st.session_state.get("esp_sig") != assinatura:
            st.session_state["esp_sig"] = assinatura
            st.session_state["esp_backend"] = EspBackend(url, user, pwd)
            st.session_state.pop("trend_cache", None)
        return st.session_state["esp_backend"]

    sim = obter_simulador()
    for k, v in PRESETS["Em repouso (parado)"].items():
        st.session_state.setdefault(f"sim_{k}", v)

    sb.markdown("---")
    sb.subheader("🎛️ Entradas digitais")
    sb.selectbox("Cenário rápido", list(PRESETS), key="sim_preset")
    sb.button("Aplicar cenário", on_click=_aplicar_preset, use_container_width=True)
    for k, rotulo in SIM_LABELS:
        sb.toggle(rotulo, key=f"sim_{k}")
    sim.set_inputs([st.session_state[f"sim_{k}"] for k, _ in SIM_LABELS])

    sb.markdown("---")
    sb.subheader("🌡️ Processo / sinal 4-20 mA")
    modo_cfg = sb.radio("Conversão do sinal",
                        ["0–3 V (4 mA = 0 V)", "Shunt 150 Ω (4 mA = 0,6 V)"])
    sim.set_config(CFG_0_3V if modo_cfg.startswith("0") else CFG_SHUNT)
    temp = sb.slider("Temperatura do processo (°C)", 0.0, 400.0, 180.0, 1.0)
    cenario = sb.selectbox("Cenário do sinal", [SCEN_NORMAL, SCEN_SAT, SCEN_OPEN])
    ruido = sb.toggle("Ruído + picos de EMI (testa a média aparada)", value=False)
    sim.set_process(temp, cenario, ruido)
    if modo_cfg.startswith("0"):
        sb.caption("Com 0–3 V, 0 mA (0 V) é lido como 0 °C: a falha 'abaixo do mínimo' só é "
                   "detectada com shunt de 150 Ω (como no comentário do firmware).")

    sb.markdown("---")
    sb.button("📈 Gerar histórico demo", on_click=sim.fill_demo_history, use_container_width=True)
    if sb.button("🔄 Reiniciar simulação", use_container_width=True):
        sim.stop()
        obter_simulador.clear()
        st.rerun()
    return sim


# =====================================================================
# MAIN
# =====================================================================
st.set_page_config(page_title="Supervisório de Queimador", page_icon="🔥", layout="wide")
st.markdown(CSS, unsafe_allow_html=True)
_backend = barra_lateral()
painel(_backend)