"""
RPL IoT Network Simulator — v4.0
Teacher-requested changes:
  1. No auto-selected nodes — user manually adds nodes & sink via buttons
  2. On startup: dialog asks how many nodes to create, then DODAG auto-builds
  3. No links shown UNTIL first DODAG run completes
  4. Sink sends DIO only to DIRECT neighbors — not all nodes
  5. Step buttons (DIS/DIO/DAO/DAO-ACK) removed from UI
  6. If parent node dies → child auto-reconnects to best available node
  7. Energy drains only when actual data packets are sent (big packets)
  8. DODAG will NOT rebuild if topology is unchanged (already formed)
  9. Tooltips on buttons, hover on nodes shows rank/parent/children
 10. Distance + formula shown in log
"""

import tkinter as tk
from tkinter import ttk, messagebox, simpledialog
import math, random, time, threading, os
from datetime import datetime

# ══════════════════════════════════════════════════════════════════
#  COLOR PALETTE
# ══════════════════════════════════════════════════════════════════
C = {
    "bg_deep":    "#05080f",
    "bg_panel":   "#080f1e",
    "bg_card":    "#0b1428",
    "bg_input":   "#060c18",
    "border":     "#1a3050",
    "border_hi":  "#285090",

    "cyan":       "#00e5ff",
    "cyan_dim":   "#0099bb",
    "blue":       "#2979ff",
    "blue_hi":    "#82b1ff",
    "teal":       "#00e676",
    "amber":      "#ffab00",
    "amber_hi":   "#ffd740",
    "red":        "#ff1744",
    "purple":     "#e040fb",
    "white":      "#ffffff",

    "sink_fill":  "#ff8f00",
    "sink_ring":  "#ffca28",

    "node_fill":  "#0d2655",
    "node_stroke":"#2979ff",
    "node_join":  "#003d1a",
    "node_join_s":"#00e676",
    "node_dead":  "#111122",
    "node_dead_s":"#333355",

    # Links only shown after DODAG formed
    "link_dodag": "#004422",
    "link_dodag_s":"#00c853",
    "route_hl":   "#76ff03",
    "area_border":"#00e5ff",

    "t_bright":   "#ffffff",
    "t_primary":  "#c8e0ff",
    "t_sec":      "#5588aa",
    "t_dim":      "#2a4060",

    "DIS":        "#ce93d8",
    "DIO":        "#82b1ff",
    "DAO":        "#ffcc02",
    "ACK":        "#69f0ae",

    "e_high":     "#00e676",
    "e_mid":      "#ffab00",
    "e_low":      "#ff1744",

    "btn_blue":   "#0d3070",
    "btn_green":  "#083020",
    "btn_red":    "#380a12",
    "btn_amber":  "#382000",
    "btn_purple": "#280a48",
    "btn_cyan":   "#083040",
}

FM = "Consolas"
FU = "Segoe UI"
NR = 26
SR = 32

# ══════════════════════════════════════════════════════════════════
#  TOOLTIP
# ══════════════════════════════════════════════════════════════════
class Tooltip:
    def __init__(self, widget, text):
        self.widget = widget
        self.text   = text
        self.tw     = None
        widget.bind("<Enter>", self.show)
        widget.bind("<Leave>", self.hide)

    def show(self, _=None):
        try:
            x = self.widget.winfo_rootx() + 30
            y = self.widget.winfo_rooty() + 30
        except Exception:
            return
        self.tw = tk.Toplevel(self.widget)
        self.tw.wm_overrideredirect(True)
        self.tw.wm_geometry(f"+{x}+{y}")
        lbl = tk.Label(self.tw, text=self.text,
                       font=(FU, 9), bg="#1a3050", fg="#ffffff",
                       relief="flat", bd=0, padx=10, pady=7,
                       justify="left", wraplength=300)
        lbl.pack()

    def hide(self, _=None):
        if self.tw:
            try: self.tw.destroy()
            except: pass
            self.tw = None


# ══════════════════════════════════════════════════════════════════
#  NODE
# ══════════════════════════════════════════════════════════════════
class Node:
    def __init__(self, nid, x, y, is_sink=False):
        self.id        = nid
        self.x, self.y = float(x), float(y)
        self.is_sink   = is_sink
        self.energy    = 100.0 if not is_sink else float('inf')
        self.rank      = 1.0   if is_sink     else float('inf')
        self.parent    = None
        self.children  = []
        self.neighbors = []          # [(Node, dist_px)]
        self.dodag_joined = is_sink
        self.alive     = True

    def dist_to(self, other):
        return math.hypot(self.x - other.x, self.y - other.y)

    def link_cost(self, other):
        """Link Cost = d_factor + e_factor"""
        d = self.dist_to(other)
        d_factor = d / 120.0
        if other.energy == float('inf'):
            e_factor = 0.0
        else:
            e_factor = max(0.0, (100.0 - other.energy) / 100.0) * 1.8
        return round(d_factor + e_factor, 4)

    def drain(self, amt):
        if not self.is_sink and self.alive:
            self.energy = max(0.0, self.energy - amt)
            if self.energy <= 0.0:
                self.alive = False
                self.rank  = float('inf')

    @property
    def rank_str(self):
        return "∞" if self.rank == float('inf') else f"{self.rank:.3f}"

    @property
    def e_color(self):
        if self.energy == float('inf'): return C["sink_fill"]
        if self.energy > 60: return C["e_high"]
        if self.energy > 25: return C["e_mid"]
        return C["e_low"]


# ══════════════════════════════════════════════════════════════════
#  RPL ENGINE
# ══════════════════════════════════════════════════════════════════
class RPLEngine:
    def __init__(self, log_fn, anim_fn, redraw_fn):
        self.nodes      = {}
        self.sink       = None
        self.log        = log_fn
        self.anim       = anim_fn
        self.redraw     = redraw_fn
        self.radio      = 230
        self.round      = 0
        self.stats      = {"DIS": 0, "DIO": 0, "DAO": 0, "DAO-ACK": 0}
        self.dodag_built = False      # True once first successful DODAG formed

    # ── Node management ──────────────────────────────────────────
    def add(self, nid, x, y, sink=False):
        n = Node(nid, x, y, sink)
        self.nodes[nid] = n
        if sink:
            self.sink = n
        self._rebuild_neighbors()
        return n

    def remove(self, nid):
        if nid not in self.nodes: return
        n = self.nodes.pop(nid)
        if n.is_sink: self.sink = None
        for o in self.nodes.values():
            o.neighbors = [(nb, d) for nb, d in o.neighbors if nb.id != nid]
            if o.parent and o.parent.id == nid:
                o.parent = None
            o.children = [c for c in o.children if c.id != nid]
        self._rebuild_neighbors()
        # If a node is removed and DODAG was built, mark it dirty
        self.dodag_built = False

    def _rebuild_neighbors(self):
        ids = list(self.nodes.keys())
        for nid in ids:
            self.nodes[nid].neighbors = []
        for i, a in enumerate(ids):
            for b in ids[i+1:]:
                na, nb = self.nodes[a], self.nodes[b]
                d = na.dist_to(nb)
                if d <= self.radio:
                    na.neighbors.append((nb, d))
                    nb.neighbors.append((na, d))

    # ── DODAG BUILD (DIO only — no broadcast from sink to all) ───
    def build_dodag(self):
        """
        Build DODAG:
        - Sink sends DIO only to its DIRECT neighbors (nodes in radio range)
        - Those neighbors propagate DIO further
        - This is correct RPL behavior
        """
        if not self.sink:
            self.log("  ✗ No Sink node! Add a Sink first.", "err")
            return False

        # Check if already built with same topology
        if self.dodag_built:
            all_joined = all(
                n.dodag_joined for n in self.nodes.values() if n.alive
            )
            if all_joined:
                self.log("  ⚠  DODAG already built for this topology.", "warn")
                self.log("  ⚠  No changes detected — DODAG not rebuilt.", "warn")
                self.log("  ⚠  Reset DODAG first to rebuild.", "warn")
                return False

        self.round += 1
        self.log("", "gap")
        self.log("╔══════════════════════════════════════════════════════╗", "hdr")
        self.log(f"║        ROUND {self.round}  —  RPL DODAG Formation              ║", "round_hdr")
        self.log("╚══════════════════════════════════════════════════════╝", "hdr")

        # ── PHASE 1: DIS ─────────────────────────────────────────
        self.log("", "gap")
        self.log("  ▌ PHASE 1 — DIS  (Node Discovery)", "phase")
        self.log("  " + "─" * 50, "phase_line")
        dis_cnt = 0
        for n in sorted(self.nodes.values(), key=lambda x: x.id):
            if n.is_sink or not n.alive or n.dodag_joined:
                continue
            self.log(f"  Node {n.id:>2}  ──DIS──▶  [BROADCAST]  "
                     f"\"Is there a DODAG?\"", "DIS")
            n.drain(0.3)
            self.stats["DIS"] += 1
            dis_cnt += 1
            self.anim(n, self.sink, "DIS")
        if dis_cnt == 0:
            self.log("  ✓ All nodes already joined — DIS skipped", "ok")
        else:
            self.log(f"  ✓ {dis_cnt} node(s) sent DIS", "ok")

        time.sleep(0.1)

        # ── PHASE 2: DIO ─────────────────────────────────────────
        # KEY FIX: Sink ONLY sends DIO to its direct neighbors in radio range
        # Not to all nodes in the network
        self.log("", "gap")
        self.log("  ▌ PHASE 2 — DIO  (DODAG Info — rank propagation)", "phase")
        self.log("  " + "─" * 50, "phase_line")
        self.log(f"  Sink (Root) sends DIO only to its {len(self.sink.neighbors)} direct neighbor(s):", "dim")

        newly_joined = []
        changed = True
        passes  = 0

        while changed and passes < 20:
            changed = False
            passes += 1
            for n in sorted(self.nodes.values(), key=lambda x: x.rank):
                if not n.dodag_joined or not n.alive:
                    continue
                for nb, _ in n.neighbors:
                    if not nb.alive or nb.dodag_joined:
                        continue
                    dist_px  = n.dist_to(nb)
                    d_factor = dist_px / 120.0
                    if nb.energy == float('inf'):
                        e_factor = 0.0
                    else:
                        e_factor = max(0.0, (100.0 - nb.energy) / 100.0) * 1.8
                    lc       = round(d_factor + e_factor, 4)
                    new_rank = round(n.rank + lc, 4)

                    if new_rank < nb.rank:
                        # Remove from old parent's children
                        if nb.parent and nb in nb.parent.children:
                            nb.parent.children.remove(nb)
                        nb.rank       = new_rank
                        nb.parent     = n
                        nb.dodag_joined = True
                        if nb not in n.children:
                            n.children.append(nb)
                        if nb not in newly_joined:
                            newly_joined.append(nb)

                        self.log(f"  Node {n.id:>2}  ──DIO──▶  Node {nb.id:>2}", "DIO")
                        self.log(f"    dist={dist_px:.1f}px  "
                                 f"d_factor={d_factor:.3f}  "
                                 f"e_factor={e_factor:.3f}  "
                                 f"LinkCost={lc:.3f}", "formula")
                        self.log(f"    Rank = {n.rank_str} + {lc:.3f} = {new_rank:.3f}"
                                 f"  ✓ Node {nb.id} joined DODAG!", "joined")
                        n.drain(0.4)
                        nb.drain(0.2)
                        self.stats["DIO"] += 1
                        self.anim(n, nb, "DIO")
                        changed = True

        total_j = sum(1 for n in self.nodes.values() if n.dodag_joined)
        self.log(f"  ✓ DODAG formed — {total_j}/{len(self.nodes)} nodes joined", "ok")
        if newly_joined:
            nj = ", ".join(f"N{n.id}" for n in newly_joined)
            self.log(f"  ★ Newly joined: {nj}", "joined")

        time.sleep(0.1)

        # ── PHASE 3: DAO ─────────────────────────────────────────
        self.log("", "gap")
        self.log("  ▌ PHASE 3 — DAO  (Route Registration)", "phase")
        self.log("  " + "─" * 50, "phase_line")
        for n in sorted(self.nodes.values(), key=lambda x: x.id):
            if n.is_sink or not n.dodag_joined or not n.alive or not n.parent:
                continue
            dist_sink = n.dist_to(self.sink) if self.sink else 0
            self.log(f"  Node {n.id:>2}  ──DAO──▶  Node {n.parent.id:>2}  "
                     f"Rank={n.rank_str}  dist_to_sink={dist_sink:.1f}px", "DAO")
            n.drain(0.5)
            self.stats["DAO"] += 1
            self.anim(n, n.parent, "DAO")

        time.sleep(0.1)

        # ── PHASE 4: DAO-ACK ─────────────────────────────────────
        self.log("", "gap")
        self.log("  ▌ PHASE 4 — DAO-ACK  (Acknowledgement)", "phase")
        self.log("  " + "─" * 50, "phase_line")
        for n in sorted(self.nodes.values(), key=lambda x: x.id):
            if n.is_sink or not n.dodag_joined or not n.alive or not n.parent:
                continue
            self.log(f"  Node {n.parent.id:>2}  ──ACK──▶  Node {n.id:>2}  ✓ Route confirmed", "ACK")
            n.parent.drain(0.4)
            self.stats["DAO-ACK"] += 1
            self.anim(n.parent, n, "DAO-ACK")

        self._summary()
        self.dodag_built = True
        return True

    # ── DATA PACKET SEND (energy drains here) ───────────────────
    def send_data(self, src_id, num_packets=1, max_dist_px=None):
        """
        Simulate sending data packets from src_id → Sink.
        num_packets  : how many packets to send (each costs energy)
        max_dist_px  : if set, only forward hops within this pixel distance
                       (stops if next hop exceeds limit)
        Energy drains on every node along the route per packet.
        """
        if src_id not in self.nodes:
            self.log(f"  ✗ Node {src_id} not found", "err")
            return
        if not self.dodag_built:
            self.log("  ✗ Build DODAG first before sending data!", "err")
            return

        n = self.nodes[src_id]
        if not n.alive:
            self.log(f"  ✗ Node {src_id} is dead!", "err")
            return
        if not n.dodag_joined:
            self.log(f"  ✗ Node {src_id} is not in DODAG!", "err")
            return

        path = self.route_to_sink(src_id)
        if not path:
            self.log(f"  ✗ No route from Node {src_id} to Sink", "err")
            return

        # Apply max_dist_px filter — truncate path where hop distance exceeds limit
        if max_dist_px is not None and max_dist_px > 0:
            filtered = [path[0]]
            for i in range(1, len(path)):
                d = path[i-1].dist_to(path[i])
                if d <= max_dist_px:
                    filtered.append(path[i])
                else:
                    self.log(f"  ⚠  Hop N{path[i-1].id}→N{path[i].id} = {d:.0f}px exceeds max {max_dist_px}px — path cut here", "warn")
                    break
            path = filtered

        ids = " → ".join(f"N{x.id}" for x in path) + " → SINK"

        for pkt_num in range(1, num_packets + 1):
            self.log("", "gap")
            self.log(f"  ▌ PACKET {pkt_num}/{num_packets}  Node {src_id} → Sink", "phase")
            self.log("  " + "─" * 50, "phase_line")
            self.log(f"  Route : {ids}", "route")
            if max_dist_px:
                self.log(f"  Max hop distance: {max_dist_px} px", "formula")
            self.log(f"  Packet size: BIG (500 bytes) — all relay nodes drain energy", "formula")

            total_cost = 0.0
            aborted = False
            for i, hop_node in enumerate(path):
                if not hop_node.alive:
                    self.log(f"  ✗ Node {hop_node.id} died mid-route! Triggering re-route...", "err")
                    self._heal_orphans()
                    self.redraw()
                    aborted = True
                    break
                drain_amt = 8.0   # Big packet = heavy drain per hop on EVERY relay node
                before = hop_node.energy
                hop_node.drain(drain_amt)
                after  = hop_node.energy
                lc     = hop_node.link_cost(path[i+1]) if i+1 < len(path) else 0
                total_cost += lc
                self.log(f"  Hop {i+1}: Node {hop_node.id}  "
                         f"energy {before:.1f}% → {after:.1f}%  (-{drain_amt:.1f})", "formula")
                if not hop_node.alive:
                    self.log(f"  ⚡ Node {hop_node.id} DIED (energy=0)!", "dead")
                    self._heal_orphans()

                self.anim(hop_node, path[i+1] if i+1 < len(path) else self.sink, "DAO")
                time.sleep(0.05)

            if not aborted:
                self.log(f"  ✓ Packet {pkt_num} delivered to Sink! Total cost: {total_cost:.3f}", "ok")
            self.redraw()

            if aborted:
                self.log(f"  ✗ Sending aborted at packet {pkt_num} due to node failure", "err")
                break

        if num_packets > 1 and not aborted:
            self.log(f"  ★ All {num_packets} packets delivered successfully!", "ok")

    # ── AUTO-HEAL: reconnect orphaned children ───────────────────
    def _heal_orphans(self):
        """
        When a parent node dies, its children become orphans.
        They must find a new best parent from available joined nodes.
        This is RPL's self-healing property.
        """
        healed = []
        for n in self.nodes.values():
            if n.is_sink or not n.alive or not n.dodag_joined:
                continue
            # Check if parent is dead or missing
            if n.parent is None or not n.parent.alive:
                old_parent_id = n.parent.id if n.parent else "None"
                # Find best new parent
                best_parent = None
                best_rank   = float('inf')
                for nb, _ in n.neighbors:
                    if nb.alive and nb.dodag_joined and nb.id != n.id:
                        candidate_rank = nb.rank + n.link_cost(nb)
                        if candidate_rank < best_rank:
                            best_rank   = candidate_rank
                            best_parent = nb
                if best_parent:
                    n.parent = best_parent
                    n.rank   = round(best_rank, 4)
                    if n not in best_parent.children:
                        best_parent.children.append(n)
                    self.log(f"  🔄 Node {n.id} re-routed: "
                             f"dead parent N{old_parent_id} → new parent N{best_parent.id}  "
                             f"new Rank={n.rank:.3f}", "joined")
                    healed.append(n.id)
                else:
                    # No alternative — node loses DODAG membership
                    n.dodag_joined = False
                    n.parent       = None
                    n.rank         = float('inf')
                    self.log(f"  ✗ Node {n.id} lost DODAG — no reachable parent", "err")

        if healed:
            self.log(f"  ✓ Auto-healed nodes: {healed}", "ok")

    # ── SUMMARY ─────────────────────────────────────────────────
    def _summary(self):
        self.log("", "gap")
        self.log("  ┌──────────────────────────────────────────────────┐", "sum_hdr")
        self.log("  │              DODAG SUMMARY                       │", "sum_hdr")
        self.log("  ├────────┬──────────┬────────┬──────────┬──────────┤", "sum_hdr")
        self.log("  │ Node   │ Rank     │ Parent │ Children │ Energy   │", "sum_hdr")
        self.log("  ├────────┼──────────┼────────┼──────────┼──────────┤", "sum_hdr")
        for nid, n in sorted(self.nodes.items()):
            if not n.alive: continue
            par  = "ROOT" if n.is_sink else (f"N{n.parent.id}" if n.parent else "—")
            kids = ",".join(str(c.id) for c in n.children) or "—"
            en   = "∞ Wire" if n.energy == float('inf') else f"{n.energy:.1f}%"
            self.log(f"  │ N{nid:<5} │ {n.rank_str:<8} │ {par:<6} │ {kids:<8} │ {en:<8} │", "sum")
        self.log("  └────────┴──────────┴────────┴──────────┴──────────┘", "sum_hdr")

    # ── ROUTE ────────────────────────────────────────────────────
    def route_to_sink(self, nid):
        if nid not in self.nodes: return []
        path, visited, cur = [self.nodes[nid]], {nid}, self.nodes[nid]
        while cur.parent and cur.parent.id not in visited:
            cur = cur.parent
            path.append(cur)
            visited.add(cur.id)
        return path

    def reset_dodag(self):
        for n in self.nodes.values():
            if not n.is_sink:
                n.rank = float('inf')
                n.parent = None
                n.children = []
                n.dodag_joined = False
                n.alive  = True
                n.energy = 100.0
        if self.sink:
            self.sink.rank     = 1.0
            self.sink.children = []
        self.round       = 0
        self.stats       = {"DIS": 0, "DIO": 0, "DAO": 0, "DAO-ACK": 0}
        self.dodag_built = False


# ══════════════════════════════════════════════════════════════════
#  MAIN APPLICATION
# ══════════════════════════════════════════════════════════════════
class App:
    def __init__(self, root):
        self.root = root
        root.title("RPL IoT Network Simulator  ●  v4.0")
        root.configure(bg=C["bg_deep"])
        root.geometry("1480x860")
        root.minsize(1280, 720)

        self.engine     = RPLEngine(self._log, self._queue_anim, self._redraw)
        self.nid_ctr    = 0
        self.sel        = None
        self.drag_n     = None
        self.drag_off   = (0, 0)
        self.route_hl   = None
        self.busy       = False
        self._pending   = None
        self._hover_win = None

        # Display toggles
        self.v_ranks  = tk.BooleanVar(value=True)
        self.v_energy = tk.BooleanVar(value=True)
        self.v_range  = tk.BooleanVar(value=False)
        self.v_cost   = tk.BooleanVar(value=True)
        self.v_dist   = tk.BooleanVar(value=True)

        self._build_ui()

        # Ask node count on startup
        self.root.after(400, self._startup_dialog)

    # ═════════════════════════════════════════════════════════════
    #  UI BUILD
    # ═════════════════════════════════════════════════════════════
    def _build_ui(self):
        # ── Topbar ───────────────────────────────────────────────
        tb = tk.Frame(self.root, bg=C["bg_panel"], height=54)
        tb.pack(fill="x"); tb.pack_propagate(False)
        tk.Frame(self.root, bg=C["cyan_dim"], height=2).pack(fill="x")

        tk.Label(tb, text="◈ RPL IoT SIMULATOR",
                 font=(FM, 16, "bold"), fg=C["cyan"],
                 bg=C["bg_panel"], padx=18).pack(side="left", pady=8)
        tk.Label(tb, text="v4.0  ·  DODAG  ·  DIS · DIO · DAO · DAO-ACK  ·  Auto-Heal",
                 font=(FM, 9), fg=C["t_sec"],
                 bg=C["bg_panel"]).pack(side="left")

        self.status_lbl = tk.Label(tb, text="●  IDLE",
                                    font=(FM, 10), fg=C["t_sec"],
                                    bg=C["bg_panel"], padx=14)
        self.status_lbl.pack(side="right")
        self.round_lbl = tk.Label(tb, text="ROUND  0",
                                   font=(FM, 14, "bold"), fg=C["amber"],
                                   bg=C["bg_panel"], padx=20)
        self.round_lbl.pack(side="right")

        # ── Body ─────────────────────────────────────────────────
        body = tk.Frame(self.root, bg=C["bg_deep"])
        body.pack(fill="both", expand=True, padx=5, pady=5)

        lp = tk.Frame(body, bg=C["bg_panel"], width=245)
        lp.pack(side="left", fill="y", padx=(0, 4))
        lp.pack_propagate(False)
        self._build_left(lp)

        rp = tk.Frame(body, bg=C["bg_panel"], width=345)
        rp.pack(side="right", fill="y", padx=(4, 0))
        rp.pack_propagate(False)
        self._build_right(rp)

        cf = tk.Frame(body, bg=C["bg_deep"])
        cf.pack(side="left", fill="both", expand=True)
        self._build_canvas(cf)

    # ── LEFT PANEL ───────────────────────────────────────────────
    def _build_left(self, p):
        sc = tk.Canvas(p, bg=C["bg_panel"], highlightthickness=0)
        sb = ttk.Scrollbar(p, orient="vertical", command=sc.yview)
        sc.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        sc.pack(side="left", fill="both", expand=True)
        inn = tk.Frame(sc, bg=C["bg_panel"])
        sc.create_window((0, 0), window=inn, anchor="nw")
        inn.bind("<Configure>",
                 lambda e: sc.configure(scrollregion=sc.bbox("all")))
        sc.bind("<MouseWheel>",
                lambda e: sc.yview_scroll(-1*(e.delta//120), "units"))

        def sec(title, color=C["cyan"]):
            tk.Frame(inn, bg=C["border"], height=1).pack(fill="x", padx=8, pady=(14,0))
            tk.Label(inn, text=f"  {title}", font=(FM, 9, "bold"),
                     fg=color, bg=C["bg_panel"]).pack(fill="x", pady=(4, 5))

        def btn(text, cmd, bg, tip="", pady=2):
            b = tk.Button(inn, text=text, command=cmd,
                          font=(FU, 9, "bold"), bg=bg, fg=C["t_bright"],
                          relief="flat", cursor="hand2", pady=9, padx=6,
                          activebackground=C["bg_card"],
                          activeforeground=C["cyan"],
                          bd=0, highlightthickness=1,
                          highlightbackground=C["border_hi"])
            b.pack(fill="x", padx=10, pady=pady)
            if tip:
                Tooltip(b, tip)
            return b

        # ── NETWORK SETUP ────────────────────────────────────────
        sec("◉  NETWORK SETUP", C["blue_hi"])
        btn("＋  Add Sensor Node", self._add_node_mode, C["btn_blue"],
            "Manually add a sensor node.\nClick this button → then click on the canvas\nwhere you want to place the node.")
        btn("⬡  Add Sink (Root)",  self._add_sink_mode, C["btn_amber"],
            "Add the Sink (Root) node — only ONE allowed.\nClick this → then click on canvas to place it.\nAll data in the network flows toward the Sink.")
        btn("✕  Remove Selected",  self._remove_sel,    C["btn_red"],
            "First click a node to select it (white ring shows),\nthen press this to remove it.")
        btn("⊘  Clear All",        self._clear_all,     C["btn_red"],
            "Remove ALL nodes and reset the simulation completely.")

        # ── GENERATE TOPOLOGY ────────────────────────────────────
        sec("◉  GENERATE TOPOLOGY", C["purple"])
        tk.Label(inn, text="  Number of Sensor Nodes:",
                 font=(FU, 8, "bold"), fg=C["t_sec"],
                 bg=C["bg_panel"]).pack(anchor="w", padx=12)

        cnt_f = tk.Frame(inn, bg=C["bg_card"],
                         highlightthickness=1,
                         highlightbackground=C["border"])
        cnt_f.pack(fill="x", padx=10, pady=4)
        self.node_count_var = tk.IntVar(value=8)
        self.count_lbl = tk.Label(cnt_f, text="8  nodes",
                                   font=(FM, 10, "bold"),
                                   fg=C["amber"], bg=C["bg_card"])
        self.count_lbl.pack(side="right", padx=10, pady=6)

        def update_count(v):
            self.count_lbl.config(text=f"{v}  nodes")
        tk.Scale(cnt_f, from_=3, to=20, orient="horizontal",
                 variable=self.node_count_var,
                 bg=C["bg_card"], fg=C["t_sec"],
                 troughcolor=C["border"],
                 activebackground=C["purple"],
                 highlightthickness=0, showvalue=False,
                 command=update_count,
                 sliderlength=14).pack(side="left", fill="x",
                                       expand=True, padx=8, pady=6)
        btn("⊞  Generate Topology", self._generate_topo, C["btn_purple"],
            "Generate a network with the selected number of nodes.\nSink is placed in center, sensor nodes placed randomly.\nYou can drag nodes after generation.")

        # ── RADIO RANGE ──────────────────────────────────────────
        sec("◉  RADIO RANGE", C["teal"])
        rng_row = tk.Frame(inn, bg=C["bg_panel"])
        rng_row.pack(fill="x", padx=10)
        tk.Label(rng_row, text="Range:", font=(FM, 8),
                 fg=C["t_sec"], bg=C["bg_panel"]).pack(side="left")
        self.range_lbl = tk.Label(rng_row, text="230 px",
                                   font=(FM, 8, "bold"),
                                   fg=C["cyan"], bg=C["bg_panel"])
        self.range_lbl.pack(side="right")
        self.range_var = tk.IntVar(value=230)
        rng_s = tk.Scale(inn, from_=60, to=460, orient="horizontal",
                         variable=self.range_var,
                         bg=C["bg_card"], fg=C["t_sec"],
                         troughcolor=C["border"],
                         activebackground=C["teal"],
                         highlightthickness=0, showvalue=False,
                         command=self._range_changed, sliderlength=14)
        rng_s.pack(fill="x", padx=10, pady=2)
        Tooltip(rng_s,
                "Wireless communication radius.\n"
                "Nodes within this distance can communicate.\n"
                "Increase to connect more nodes.")

        # ── SIMULATION ───────────────────────────────────────────
        sec("◉  SIMULATION", C["teal"])
        btn("▶  Build DODAG", self._run_dodag, C["btn_green"],
            "Run the full RPL DODAG formation:\n"
            "DIS → DIO → DAO → DAO-ACK\n\n"
            "• Sink sends DIO only to direct neighbors\n"
            "• Each node picks best parent (lowest rank)\n"
            "• DODAG will NOT rebuild if already formed\n"
            "  (Reset first to rebuild)")
        btn("📦  Send Data Packet", self._send_data_dialog, C["btn_cyan"],
            "Simulate sending a big data packet from a node → Sink.\n"
            "Energy drains significantly per hop (big packet = 8% per hop).\n"
            "If a relay node dies mid-route, auto-heal triggers.")
        btn("↺  Reset DODAG", self._reset, C["btn_red"],
            "Reset all ranks, parents, and energy levels.\n"
            "Nodes stay on canvas.\n"
            "Run Build DODAG again after reset.")

        # ── DISPLAY ──────────────────────────────────────────────
        sec("◉  DISPLAY", C["purple"])
        for txt, var, tip in [
            ("Show Ranks",        self.v_ranks,
             "Show rank value below each node (R:x.xxx).\nLower rank = closer to Sink."),
            ("Show Energy Bars",  self.v_energy,
             "Show battery % bar below each node.\nGreen=high  Amber=mid  Red=low"),
            ("Show Radio Range",  self.v_range,
             "Show wireless communication range circle."),
            ("Show Link Cost",    self.v_cost,
             "Show link cost value on DODAG connections."),
            ("Show Dist to Sink", self.v_dist,
             "Show pixel distance from each node to the Sink."),
        ]:
            cb = tk.Checkbutton(inn, text=f"  {txt}", variable=var,
                                command=self._redraw,
                                font=(FU, 9), fg=C["t_primary"],
                                bg=C["bg_panel"], selectcolor=C["bg_card"],
                                activebackground=C["bg_panel"],
                                activeforeground=C["cyan"],
                                cursor="hand2")
            cb.pack(anchor="w", padx=12, pady=1)
            Tooltip(cb, tip)

        # ── ROUTE TRACE ──────────────────────────────────────────
        sec("◉  ROUTE TRACE", C["amber"])
        rt_f = tk.Frame(inn, bg=C["bg_card"],
                        highlightthickness=1,
                        highlightbackground=C["border"])
        rt_f.pack(fill="x", padx=10, pady=4)
        tk.Label(rt_f, text=" From Node ID:", font=(FM, 8),
                 fg=C["t_sec"], bg=C["bg_card"]).pack(side="left",
                                                       padx=4, pady=6)
        self.route_entry = tk.Entry(rt_f, font=(FM, 10, "bold"),
                                    bg=C["bg_input"], fg=C["amber"],
                                    insertbackground=C["amber"],
                                    relief="flat", width=5,
                                    highlightthickness=0)
        self.route_entry.pack(side="right", padx=6, pady=4)
        btn("🗺  Trace Route → Sink", self._trace_route, C["btn_amber"],
            "Enter a Node ID and highlight its best path to the Sink.\nShown as a bright green dashed line on canvas.")

        # ── MSG STATS ────────────────────────────────────────────
        sec("◉  MESSAGE STATS", C["teal"])
        sf = tk.Frame(inn, bg=C["bg_card"],
                      highlightthickness=1,
                      highlightbackground=C["border"])
        sf.pack(fill="x", padx=10, pady=4)
        self._stat_lbl = {}
        for msg, col, tip in [
            ("DIS",     C["DIS"],
             "DIS = DODAG Information Solicitation\nUnjoined nodes broadcast to find DODAG"),
            ("DIO",     C["DIO"],
             "DIO = DODAG Information Object\nPropagates rank info to build the tree"),
            ("DAO",     C["DAO"],
             "DAO = Destination Advertisement Object\nNodes register routes with parents"),
            ("DAO-ACK", C["ACK"],
             "DAO-ACK = Acknowledgement\nParents confirm route registration"),
        ]:
            row = tk.Frame(sf, bg=C["bg_card"])
            row.pack(fill="x", padx=8, pady=3)
            dot = tk.Label(row, text="●", font=(FM, 11),
                           fg=col, bg=C["bg_card"])
            dot.pack(side="left")
            Tooltip(dot, tip)
            tk.Label(row, text=f" {msg}", font=(FM, 9, "bold"),
                     fg=col, bg=C["bg_card"], width=7,
                     anchor="w").pack(side="left")
            lbl = tk.Label(row, text="0", font=(FM, 11, "bold"),
                           fg=C["t_bright"], bg=C["bg_card"])
            lbl.pack(side="right")
            self._stat_lbl[msg] = lbl

        # ── SCREENSHOT ───────────────────────────────────────────
        sec("◉  SCREENSHOT", C["amber_hi"] if "amber_hi" in C else C["amber"])
        btn("📷  Save Screenshot", self._screenshot, C["btn_amber"],
            "Save a PNG/PS image of the network canvas.\nSaved to Desktop (or current folder).")

        tk.Frame(inn, bg=C["bg_panel"], height=20).pack()

    # ── CANVAS ───────────────────────────────────────────────────
    def _build_canvas(self, parent):
        hdr = tk.Frame(parent, bg=C["bg_deep"])
        hdr.pack(fill="x")
        tk.Label(hdr,
                 text="  DODAG NETWORK TOPOLOGY"
                      "  ·  Drag nodes to reposition"
                      "  ·  Hover node for details"
                      "  ·  Right-click for options",
                 font=(FM, 8), fg=C["t_sec"],
                 bg=C["bg_deep"]).pack(side="left", pady=(0, 3))

        outer = tk.Frame(parent, bg=C["cyan_dim"], bd=1)
        outer.pack(fill="both", expand=True)
        inner = tk.Frame(outer, bg=C["bg_deep"])
        inner.pack(fill="both", expand=True, padx=1, pady=1)

        self.canvas = tk.Canvas(inner, bg=C["bg_deep"],
                                highlightthickness=0, cursor="crosshair")
        self.canvas.pack(fill="both", expand=True)

        self.canvas.bind("<Button-1>",        self._cv_click)
        self.canvas.bind("<B1-Motion>",       self._cv_drag)
        self.canvas.bind("<ButtonRelease-1>", self._cv_release)
        self.canvas.bind("<Button-3>",        self._cv_right)
        self.canvas.bind("<Motion>",          self._cv_hover)
        self.canvas.bind("<Configure>",       lambda e: self._full_redraw())

        leg = tk.Frame(parent, bg=C["bg_panel"], height=28)
        leg.pack(fill="x"); leg.pack_propagate(False)
        for txt, col in [
            ("⬡ Sink",   C["sink_fill"]),
            ("● Node",   C["node_stroke"]),
            ("● Joined", C["node_join_s"]),
            ("─ DODAG",  C["link_dodag_s"]),
            ("DIS",      C["DIS"]),
            ("DIO",      C["DIO"]),
            ("DAO",      C["DAO"]),
            ("ACK",      C["ACK"]),
            ("⚡ Route", C["route_hl"]),
        ]:
            tk.Label(leg, text=f"  {txt}", font=(FM, 8),
                     fg=col, bg=C["bg_panel"]).pack(side="left")

    # ── RIGHT PANEL ──────────────────────────────────────────────
    def _build_right(self, p):
        hdr_row = tk.Frame(p, bg=C["bg_panel"])
        hdr_row.pack(fill="x", pady=(10, 0), padx=6)
        tk.Label(hdr_row, text="◈  PROTOCOL LOG",
                 font=(FM, 10, "bold"), fg=C["cyan"],
                 bg=C["bg_panel"]).pack(side="left")
        tk.Button(hdr_row, text="⌫ Clear", command=self._clear_log,
                  font=(FU, 8), bg=C["btn_red"], fg=C["t_sec"],
                  relief="flat", cursor="hand2", padx=8, pady=3,
                  activebackground=C["red"],
                  activeforeground=C["white"]).pack(side="right")

        tk.Frame(p, bg=C["cyan_dim"], height=1).pack(fill="x", padx=6, pady=(3, 0))

        lf = tk.Frame(p, bg=C["bg_card"])
        lf.pack(fill="both", expand=True, padx=5, pady=4)

        self.log_box = tk.Text(lf, font=(FM, 8),
                               bg=C["bg_input"], fg=C["t_primary"],
                               insertbackground=C["cyan"],
                               relief="flat", wrap="none",
                               state="disabled",
                               padx=6, pady=4,
                               spacing1=1, spacing3=1)
        vsb = ttk.Scrollbar(lf, orient="vertical",   command=self.log_box.yview)
        hsb = ttk.Scrollbar(lf, orient="horizontal", command=self.log_box.xview)
        self.log_box.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        vsb.pack(side="right", fill="y")
        hsb.pack(side="bottom", fill="x")
        self.log_box.pack(fill="both", expand=True)

        # Tags
        tags = {
            "hdr":        (C["cyan"],    True),
            "round_hdr":  (C["amber"],   True),
            "phase":      (C["blue_hi"], True),
            "phase_line": (C["t_dim"],   False),
            "DIS":        (C["DIS"],     True),
            "DIO":        (C["DIO"],     True),
            "DAO":        (C["DAO"],     True),
            "ACK":        (C["ACK"],     True),
            "formula":    ("#607d8b",    False),
            "joined":     (C["teal"],    True),
            "ok":         (C["teal"],    False),
            "warn":       (C["amber"],   False),
            "err":        (C["red"],     True),
            "dead":       (C["red"],     True),
            "sum_hdr":    (C["blue_hi"], True),
            "sum":        (C["t_primary"], False),
            "route":      (C["route_hl"], True),
            "dim":        (C["t_sec"],   False),
            "info":       (C["t_primary"], False),
            "gap":        (C["bg_deep"], False),
        }
        for tag, (col, bold) in tags.items():
            kw = {"foreground": col}
            if bold:
                kw["font"] = (FM, 8, "bold")
            self.log_box.tag_configure(tag, **kw)

        # Inspector
        tk.Label(p, text="◈  NODE INSPECTOR  (click any node)",
                 font=(FM, 9, "bold"), fg=C["cyan"],
                 bg=C["bg_panel"]).pack(fill="x", padx=6, pady=(4, 2))
        tk.Frame(p, bg=C["cyan_dim"], height=1).pack(fill="x", padx=6)

        self.inspector = tk.Text(p, font=(FM, 8),
                                 bg=C["bg_input"], fg=C["t_primary"],
                                 relief="flat", state="disabled",
                                 height=13, padx=8, pady=5)
        self.inspector.pack(fill="x", padx=5, pady=(4, 5))
        for tag, col, bold in [
            ("key",   C["t_sec"],    False),
            ("val",   C["t_bright"], False),
            ("hi",    C["cyan"],     True),
            ("teal",  C["teal"],     False),
            ("amber", C["amber"],    False),
            ("red",   C["red"],      False),
            ("blue",  C["blue_hi"],  False),
        ]:
            kw = {"foreground": col}
            if bold: kw["font"] = (FM, 8, "bold")
            self.inspector.tag_configure(tag, **kw)

    # ═════════════════════════════════════════════════════════════
    #  STARTUP DIALOG
    # ═════════════════════════════════════════════════════════════
    def _startup_dialog(self):
        """Ask user how many nodes they want on startup"""
        dlg = tk.Toplevel(self.root)
        dlg.title("RPL Simulator — Network Setup")
        dlg.configure(bg=C["bg_panel"])
        dlg.resizable(False, False)
        dlg.grab_set()

        # Center it
        dlg.geometry("420x320")
        dlg.update_idletasks()
        x = (dlg.winfo_screenwidth()  // 2) - 210
        y = (dlg.winfo_screenheight() // 2) - 160
        dlg.geometry(f"420x320+{x}+{y}")

        tk.Label(dlg, text="◈ RPL IoT Network Simulator",
                 font=(FM, 14, "bold"), fg=C["cyan"],
                 bg=C["bg_panel"]).pack(pady=(20, 4))
        tk.Frame(dlg, bg=C["cyan_dim"], height=1).pack(fill="x", padx=20)
        tk.Label(dlg,
                 text="How many sensor nodes do you want\n"
                      "in your network?",
                 font=(FU, 11), fg=C["t_primary"],
                 bg=C["bg_panel"]).pack(pady=(16, 4))

        count_var = tk.IntVar(value=8)
        count_lbl = tk.Label(dlg, text="8",
                             font=(FM, 28, "bold"),
                             fg=C["amber"], bg=C["bg_panel"])
        count_lbl.pack()

        def on_scale(v):
            count_lbl.config(text=str(int(float(v))))

        tk.Scale(dlg, from_=3, to=20, orient="horizontal",
                 variable=count_var,
                 bg=C["bg_panel"], fg=C["t_sec"],
                 troughcolor=C["border"],
                 activebackground=C["amber"],
                 highlightthickness=0, showvalue=False,
                 length=300, sliderlength=18,
                 command=on_scale).pack(pady=4)

        tk.Label(dlg, text="(3 – 20 nodes)",
                 font=(FU, 9), fg=C["t_sec"],
                 bg=C["bg_panel"]).pack()

        def on_generate():
            n = count_var.get()
            dlg.destroy()
            self._generate_with_count(n)

        def on_manual():
            dlg.destroy()
            self._log("  ✓ Manual mode — use buttons to add nodes & sink", "ok")
            self._log("  ► Add Sink first, then Sensor Nodes", "dim")
            self._log("  ► Then press 'Build DODAG' to run simulation", "dim")

        btn_frame = tk.Frame(dlg, bg=C["bg_panel"])
        btn_frame.pack(pady=16)
        tk.Button(btn_frame, text="⊞  Generate Network",
                  command=on_generate,
                  font=(FU, 10, "bold"), bg=C["btn_green"],
                  fg=C["t_bright"], relief="flat", cursor="hand2",
                  padx=16, pady=9,
                  activebackground=C["teal"],
                  activeforeground=C["white"]).pack(side="left", padx=6)
        tk.Button(btn_frame, text="✎  Manual Setup",
                  command=on_manual,
                  font=(FU, 10, "bold"), bg=C["btn_blue"],
                  fg=C["t_bright"], relief="flat", cursor="hand2",
                  padx=16, pady=9,
                  activebackground=C["blue"],
                  activeforeground=C["white"]).pack(side="left", padx=6)

    # ═════════════════════════════════════════════════════════════
    #  DRAWING
    # ═════════════════════════════════════════════════════════════
    def _full_redraw(self):
        self.canvas.delete("all")
        self._draw_bg()
        self._draw_links()
        self._draw_route()
        self._draw_nodes()

    def _redraw(self, *_):
        self._full_redraw()

    def _draw_bg(self):
        w = self.canvas.winfo_width()
        h = self.canvas.winfo_height()
        for x in range(0, w, 36):
            for y in range(0, h, 36):
                self.canvas.create_rectangle(x, y, x+1, y+1,
                                             fill="#0f1e35", outline="")

    def _draw_links(self):
        """
        KEY: Links are ONLY drawn after DODAG is built.
        Before DODAG, nodes show but NO connecting lines.
        """
        if not self.engine.dodag_built:
            return   # ← No links shown before DODAG formation

        drawn = set()
        for nid, n in self.engine.nodes.items():
            for nb, _ in n.neighbors:
                key = tuple(sorted([nid, nb.id]))
                if key in drawn:
                    continue
                drawn.add(key)
                is_dag = (n.parent == nb or nb.parent == n)
                if is_dag:
                    # DODAG parent link — thick + glow
                    self.canvas.create_line(n.x, n.y, nb.x, nb.y,
                                            fill=C["link_dodag"], width=5)
                    self.canvas.create_line(n.x, n.y, nb.x, nb.y,
                                            fill=C["link_dodag_s"], width=1,
                                            dash=(6, 3))
                    if self.v_cost.get():
                        mx = (n.x + nb.x) / 2
                        my = (n.y + nb.y) / 2
                        lc = n.link_cost(nb)
                        self.canvas.create_text(
                            mx, my - 9,
                            text=f"{lc:.3f}",
                            font=(FM, 7), fill=C["t_dim"])

        if self.v_range.get():
            r = self.engine.radio
            for n in self.engine.nodes.values():
                if n.alive:
                    self.canvas.create_oval(
                        n.x-r, n.y-r, n.x+r, n.y+r,
                        outline=C["border_hi"], width=1, dash=(3, 6))

    def _draw_route(self):
        if not self.route_hl or len(self.route_hl) < 2:
            return
        for i in range(len(self.route_hl) - 1):
            a, b = self.route_hl[i], self.route_hl[i+1]
            self.canvas.create_line(a.x, a.y, b.x, b.y,
                                    fill=C["route_hl"], width=7, dash=(8, 3))
            self.canvas.create_line(a.x, a.y, b.x, b.y,
                                    fill=C["white"], width=1, dash=(8, 3))

    def _draw_nodes(self):
        for n in self.engine.nodes.values():
            self._draw_one(n)

    def _draw_one(self, n):
        x, y = n.x, n.y
        is_sel = self.sel and self.sel.id == n.id

        if n.is_sink:
            for ri in [SR+18, SR+10]:
                self.canvas.create_oval(x-ri, y-ri, x+ri, y+ri,
                                        fill="", outline=C["amber"],
                                        width=1)
            self.canvas.create_oval(x-SR, y-SR, x+SR, y+SR,
                                    fill=C["sink_fill"],
                                    outline=C["sink_ring"], width=3)
            self.canvas.create_text(x, y, text="⬡",
                                    font=(FM, 20, "bold"),
                                    fill=C["bg_deep"])
            self.canvas.create_text(x, y+SR+14,
                                    text="SINK  R:1.0",
                                    font=(FM, 8, "bold"),
                                    fill=C["amber_hi"])
            if self.v_dist.get():
                self.canvas.create_text(x, y+SR+26,
                                        text="dist: 0 px",
                                        font=(FM, 7), fill=C["t_sec"])
            return

        if not n.alive:
            self.canvas.create_oval(x-NR, y-NR, x+NR, y+NR,
                                    fill=C["node_dead"],
                                    outline=C["node_dead_s"], width=2)
            self.canvas.create_text(x, y, text="✕",
                                    font=(FM, 13, "bold"),
                                    fill=C["t_sec"])
            self.canvas.create_text(x, y+NR+12,
                                    text=f"N{n.id} DEAD",
                                    font=(FM, 7), fill=C["t_sec"])
            return

        if is_sel:
            self.canvas.create_oval(x-NR-7, y-NR-7,
                                    x+NR+7, y+NR+7,
                                    fill="", outline=C["white"],
                                    width=2, dash=(4, 2))

        fill_c  = C["node_join"]   if n.dodag_joined else C["node_fill"]
        ring_c  = C["node_join_s"] if n.dodag_joined else C["node_stroke"]

        self.canvas.create_oval(x-NR-3, y-NR-3, x+NR+3, y+NR+3,
                                fill="", outline=ring_c, width=1)
        self.canvas.create_oval(x-NR, y-NR, x+NR, y+NR,
                                fill=fill_c, outline=ring_c, width=2)
        self.canvas.create_text(x, y, text=f"N{n.id}",
                                font=(FM, 10, "bold"), fill=C["t_bright"])

        oy = NR + 12
        if self.v_ranks.get():
            self.canvas.create_text(x, y+oy,
                                    text=f"R:{n.rank_str}",
                                    font=(FM, 7, "bold"), fill=C["amber"])
            oy += 12

        if self.v_dist.get() and n.parent:
            # Only show distance when DODAG is built and parent exists
            d = n.dist_to(n.parent)
            label_txt = f"d→N{n.parent.id}:{d:.0f}px"
            self.canvas.create_text(x, y+oy,
                                    text=label_txt,
                                    font=(FM, 7), fill=C["t_sec"])
            oy += 11

        if self.v_energy.get():
            bw = 36; bh = 5
            bx = x - bw//2; by = y+oy
            self.canvas.create_rectangle(bx, by, bx+bw, by+bh,
                                         fill=C["bg_deep"],
                                         outline=C["border"])
            fw = max(1, int(bw * n.energy / 100))
            self.canvas.create_rectangle(bx, by, bx+fw, by+bh,
                                         fill=n.e_color, outline="")
            self.canvas.create_text(x, by+bh+7,
                                    text=f"{n.energy:.0f}%",
                                    font=(FM, 7), fill=n.e_color)

    # ═════════════════════════════════════════════════════════════
    #  ANIMATION
    # ═════════════════════════════════════════════════════════════
    def _queue_anim(self, src, dst, mtype):
        self.root.after(0, lambda: self._anim(src, dst, mtype))

    def _anim(self, src, dst, mtype):
        color = C.get(mtype, C["white"])
        steps = 20
        dx = (dst.x - src.x) / steps
        dy = (dst.y - src.y) / steps
        dot   = self.canvas.create_oval(src.x-7, src.y-7,
                                         src.x+7, src.y+7,
                                         fill=color, outline=C["white"], width=1)
        label = self.canvas.create_text(src.x, src.y-16,
                                         text=mtype,
                                         font=(FM, 7, "bold"), fill=color)
        trail = self.canvas.create_line(src.x, src.y, src.x, src.y,
                                         fill=color, width=1, dash=(3, 5))

        def step(i, px, py):
            if i >= steps:
                self.canvas.delete(dot)
                self.canvas.delete(label)
                self.canvas.delete(trail)
                return
            nx, ny = px+dx, py+dy
            self.canvas.coords(dot,   nx-7, ny-7, nx+7, ny+7)
            self.canvas.coords(label, nx, ny-16)
            self.canvas.coords(trail, src.x, src.y, nx, ny)
            self.root.after(28, lambda: step(i+1, nx, ny))

        step(0, src.x, src.y)

    # ═════════════════════════════════════════════════════════════
    #  CANVAS EVENTS
    # ═════════════════════════════════════════════════════════════
    def _node_at(self, x, y):
        for n in self.engine.nodes.values():
            r = SR if n.is_sink else NR
            if math.hypot(x - n.x, y - n.y) <= r + 6:
                return n
        return None

    def _cv_click(self, e):
        if self._pending:
            self._place(e.x, e.y)
            return
        n = self._node_at(e.x, e.y)
        self.sel    = n
        self.drag_n = n
        if n:
            self.drag_off = (e.x - n.x, e.y - n.y)
            self._inspect(n)
        else:
            self.route_hl = None
        self._redraw()

    def _cv_drag(self, e):
        if self.drag_n:
            self.drag_n.x = e.x - self.drag_off[0]
            self.drag_n.y = e.y - self.drag_off[1]
            self.engine._rebuild_neighbors()
            self._redraw()

    def _cv_release(self, e):
        self.drag_n = None

    def _cv_right(self, e):
        n = self._node_at(e.x, e.y)
        if not n: return
        self.sel = n; self._redraw()
        m = tk.Menu(self.root, tearoff=0,
                    bg=C["bg_card"], fg=C["t_bright"],
                    activebackground=C["btn_blue"],
                    activeforeground=C["white"],
                    font=(FU, 9))
        m.add_command(label=f"  Node {n.id}  —  Inspect",
                      command=lambda: self._inspect(n))
        m.add_command(label="  Trace Route → Sink",
                      command=lambda: self._do_trace(n.id))
        m.add_command(label="  Send Data from this Node",
                      command=lambda: self._send_data_from(n.id))
        m.add_separator()
        m.add_command(label="  ✕  Remove Node",
                      command=lambda: self._del_node(n.id))
        m.post(e.x_root, e.y_root)

    def _cv_hover(self, e):
        n = self._node_at(e.x, e.y)
        if n:
            self.canvas.config(cursor="hand2")
            self._show_hover(e, n)
        else:
            self.canvas.config(cursor="crosshair")
            self._hide_hover()

    def _show_hover(self, e, n):
        self._hide_hover()
        tw = tk.Toplevel(self.root)
        tw.wm_overrideredirect(True)
        tw.wm_geometry(f"+{e.x_root+16}+{e.y_root+16}")
        tw.configure(bg=C["bg_card"])
        f = tk.Frame(tw, bg=C["bg_card"],
                     highlightthickness=1,
                     highlightbackground=C["border_hi"])
        f.pack()
        par  = "ROOT" if n.is_sink else (f"Node {n.parent.id}" if n.parent else "None")
        kids = ", ".join(f"N{c.id}" for c in n.children) or "None"
        nbs  = ", ".join(f"N{nb.id}" for nb, _ in n.neighbors) or "None"
        en   = "∞ Wired" if n.energy == float('inf') else f"{n.energy:.1f}%"
        d2s  = "0 px" if n.is_sink else (
            f"{n.dist_to(self.engine.sink):.1f} px"
            if self.engine.sink else "N/A")
        if n.is_sink:
            d2p = "— (Root)"
        elif n.parent:
            d2p = f"{n.dist_to(n.parent):.1f} px  (→ N{n.parent.id})"
        elif self.engine.sink:
            d2p = "—"
        else:
            d2p = "—"
        kind = "SINK (Root)" if n.is_sink else "Sensor Node"

        lines = [
            ("━━━━━━ NODE INFO ━━━━━━", C["cyan"]),
            (f"  ID          :  {n.id}", C["t_bright"]),
            (f"  Type        :  {kind}", C["blue_hi"]),
            (f"  DODAG       :  {'✓ Joined' if n.dodag_joined else '○ Not Joined'}",
             C["teal"] if n.dodag_joined else C["t_sec"]),
            (f"  Rank        :  {n.rank_str}", C["amber"]),
            (f"  Dist→Parent :  {d2p}", C["t_primary"]),
            (f"  Energy      :  {en}", n.e_color),
            (f"  Parent      :  {par}", C["blue_hi"]),
            (f"  Children    :  {kids}", C["teal"]),
            (f"  Neighbors   :  {nbs}", C["t_sec"]),
        ]
        for txt, col in lines:
            tk.Label(f, text=txt, font=(FM, 8),
                     fg=col, bg=C["bg_card"],
                     anchor="w", padx=10, pady=1).pack(fill="x")
        self._hover_win = tw

    def _hide_hover(self):
        if self._hover_win:
            try: self._hover_win.destroy()
            except: pass
            self._hover_win = None

    # ═════════════════════════════════════════════════════════════
    #  BUTTON HANDLERS
    # ═════════════════════════════════════════════════════════════
    def _add_node_mode(self):
        self._pending = "node"
        self.canvas.config(cursor="plus")
        self._set_status("Click canvas to place Sensor Node", C["blue_hi"])

    def _add_sink_mode(self):
        if self.engine.sink:
            messagebox.showwarning("Sink Exists",
                "A Sink already exists.\nRemove it first."); return
        self._pending = "sink"
        self.canvas.config(cursor="plus")
        self._set_status("Click canvas to place Sink Node", C["amber"])

    def _place(self, x, y):
        self.nid_ctr += 1
        is_sink = (self._pending == "sink")
        n = self.engine.add(self.nid_ctr, x, y, is_sink)
        kind = "SINK (Root)" if is_sink else f"Sensor Node {n.id}"
        self._log(f"  ✓ {kind} added at ({x:.0f}, {y:.0f})", "ok")
        self._pending = None
        self.canvas.config(cursor="crosshair")
        self._set_status("IDLE", C["t_sec"])
        self._redraw()
        self._update_stats()

    def _remove_sel(self):
        if self.sel:
            self._del_node(self.sel.id)
        else:
            messagebox.showinfo("No selection",
                                "Click a node first to select it.")

    def _del_node(self, nid):
        self.engine.remove(nid)
        self.sel = None; self.route_hl = None
        self._log(f"  ✕ Removed Node {nid}", "dim")
        self._redraw()

    def _generate_topo(self):
        self._generate_with_count(self.node_count_var.get())

    def _generate_with_count(self, cnt):
        self._clear_all()
        w = self.canvas.winfo_width()  or 760
        h = self.canvas.winfo_height() or 520
        pad = 70

        # Sink in center
        self.nid_ctr += 1
        self.engine.add(self.nid_ctr, w//2, h//2, True)

        # Sensor nodes randomly placed
        for _ in range(cnt):
            self.nid_ctr += 1
            self.engine.add(self.nid_ctr,
                            random.randint(pad, w - pad),
                            random.randint(pad, h - pad))

        self._log("", "gap")
        self._log(f"  ✓ Network generated: 1 Sink + {cnt} Sensor Nodes", "ok")
        self._log(f"  ✓ Total nodes: {cnt + 1}", "dim")
        self._log("  ► Press 'Build DODAG' to run simulation", "dim")
        self._log("  ► Drag nodes to reposition before running", "dim")
        self._redraw()
        self._update_stats()

    def _clear_all(self):
        self.engine.nodes.clear()
        self.engine.sink = None
        self.nid_ctr     = 0
        self.sel         = None
        self.route_hl    = None
        self.engine.round       = 0
        self.engine.stats       = {"DIS": 0, "DIO": 0, "DAO": 0, "DAO-ACK": 0}
        self.engine.dodag_built = False
        self.round_lbl.config(text="ROUND  0")
        self._redraw()
        self._update_stats()
        self._log("  ✓ Canvas cleared", "dim")

    def _run_dodag(self):
        if not self.engine.sink:
            messagebox.showwarning("No Sink",
                "Please add a Sink (Root) node first!"); return
        if len(self.engine.nodes) < 2:
            messagebox.showwarning("Too few nodes",
                "Add at least 2 nodes before building DODAG."); return
        if self.busy: return
        self.busy = True
        self._set_status("BUILDING DODAG…", C["teal"])

        def _work():
            result = self.engine.build_dodag()
            self.root.after(0, lambda: self._post_dodag(result))

        threading.Thread(target=_work, daemon=True).start()

    def _post_dodag(self, built):
        self.busy = False
        self.round_lbl.config(text=f"ROUND  {self.engine.round}")
        self._set_status("IDLE", C["t_sec"])
        self._redraw()
        self._update_stats()

    def _send_data_dialog(self):
        if not self.engine.dodag_built:
            messagebox.showwarning("DODAG not built",
                "Build DODAG first!"); return

        # Custom dialog: Node ID, packet count, max hop distance
        dlg = tk.Toplevel(self.root)
        dlg.title("Send Data Packet")
        dlg.configure(bg=C["bg_panel"])
        dlg.resizable(False, False)
        dlg.grab_set()
        dlg.geometry("390x300")
        dlg.update_idletasks()
        x = (dlg.winfo_screenwidth() // 2) - 195
        y = (dlg.winfo_screenheight() // 2) - 150
        dlg.geometry(f"390x300+{x}+{y}")

        tk.Label(dlg, text="◈  Send Data Packet",
                 font=(FM, 13, "bold"), fg=C["cyan"],
                 bg=C["bg_panel"]).pack(pady=(14, 4))
        tk.Frame(dlg, bg=C["cyan_dim"], height=1).pack(fill="x", padx=20)

        def make_field(parent, lbl_txt, default, hint):
            row = tk.Frame(parent, bg=C["bg_panel"])
            row.pack(fill="x", padx=24, pady=7)
            tk.Label(row, text=lbl_txt, font=(FU, 10, "bold"),
                     fg=C["t_sec"], bg=C["bg_panel"], width=20,
                     anchor="w").pack(side="left")
            var = tk.StringVar(value=str(default))
            tk.Entry(row, textvariable=var, font=(FM, 11, "bold"),
                     bg=C["bg_input"], fg=C["amber"],
                     insertbackground=C["amber"], relief="flat",
                     highlightthickness=1,
                     highlightbackground=C["border"], width=7).pack(side="left", padx=6)
            tk.Label(row, text=hint, font=(FU, 8),
                     fg=C["t_dim"], bg=C["bg_panel"]).pack(side="left")
            return var

        nid_var  = make_field(dlg, "Source Node ID :", "",  "required")
        pkt_var  = make_field(dlg, "Num Packets    :", 1,   "( 1 – 20 )")
        dist_var = make_field(dlg, "Max Hop Dist   :", 0,   "px  ( 0 = no limit )")

        result = [None]

        def on_send():
            try:
                nid = int(nid_var.get().strip())
            except ValueError:
                messagebox.showerror("Invalid", "Enter a numeric Node ID", parent=dlg); return
            try:
                npkts = max(1, min(20, int(pkt_var.get().strip())))
            except ValueError:
                messagebox.showerror("Invalid", "Packet count must be 1–20", parent=dlg); return
            try:
                md = int(dist_var.get().strip())
                md = None if md <= 0 else md
            except ValueError:
                messagebox.showerror("Invalid", "Max dist must be a number (0=no limit)", parent=dlg); return
            result[0] = (nid, npkts, md)
            dlg.destroy()

        def on_cancel():
            dlg.destroy()

        btn_row = tk.Frame(dlg, bg=C["bg_panel"])
        btn_row.pack(pady=14)
        tk.Button(btn_row, text="📦  Send", command=on_send,
                  font=(FU, 10, "bold"), bg=C["btn_cyan"],
                  fg=C["t_bright"], relief="flat", cursor="hand2",
                  padx=18, pady=8,
                  activebackground=C["cyan_dim"],
                  activeforeground=C["white"]).pack(side="left", padx=8)
        tk.Button(btn_row, text="Cancel", command=on_cancel,
                  font=(FU, 10), bg=C["btn_red"],
                  fg=C["t_sec"], relief="flat", cursor="hand2",
                  padx=14, pady=8).pack(side="left", padx=8)

        dlg.wait_window()
        if result[0]:
            nid, npkts, md = result[0]
            self._send_data_from(nid, npkts, md)

    def _send_data_from(self, nid, num_packets=1, max_dist_px=None):
        if self.busy: return
        self.busy = True
        self._set_status(f"Sending {num_packets} pkt(s) from N{nid}…", C["DAO"])

        def _work():
            self.engine.send_data(nid, num_packets, max_dist_px)
            self.root.after(0, self._post_dodag_no_count)

        threading.Thread(target=_work, daemon=True).start()

    def _post_dodag_no_count(self):
        self.busy = False
        self._set_status("IDLE", C["t_sec"])
        self._redraw()
        self._update_stats()

    def _reset(self):
        self.engine.reset_dodag()
        self.route_hl = None
        self.round_lbl.config(text="ROUND  0")
        self._log("  ↺ DODAG reset — ranks, energy & parents cleared", "dim")
        self._log("  ► Press 'Build DODAG' to rebuild", "dim")
        self._redraw()
        self._update_stats()

    def _trace_route(self):
        try:
            nid = int(self.route_entry.get().strip())
        except ValueError:
            messagebox.showwarning("Invalid", "Enter a valid Node ID"); return
        self._do_trace(nid)

    def _do_trace(self, nid):
        path = self.engine.route_to_sink(nid)
        if not path:
            self._log(f"  ✗ No route from Node {nid} — run DODAG first!", "err")
            return
        self.route_hl = path
        ids = " → ".join(f"N{n.id}" for n in path) + " → SINK"
        self._log("", "gap")
        self._log(f"  🗺  ROUTE: {ids}", "route")
        total = 0.0
        for i in range(len(path) - 1):
            a, b = path[i], path[i+1]
            lc = a.link_cost(b)
            d  = a.dist_to(b)
            total += lc
            self._log(f"  N{a.id}→N{b.id}  dist={d:.1f}px  cost={lc:.4f}", "dim")
        self._log(f"  Total cost: {total:.4f}  |  Hops: {len(path)-1}", "route")
        self._redraw()

    def _range_changed(self, v):
        self.engine.radio = int(v)
        self.range_lbl.config(text=f"{v} px")
        self.engine._rebuild_neighbors()
        self._redraw()

    def _screenshot(self):
        try:
            from PIL import ImageGrab
            x = self.canvas.winfo_rootx()
            y = self.canvas.winfo_rooty()
            w = x + self.canvas.winfo_width()
            h = y + self.canvas.winfo_height()
            img = ImageGrab.grab(bbox=(x, y, w, h))
            ts  = datetime.now().strftime("%Y%m%d_%H%M%S")
            desk = os.path.join(os.path.expanduser("~"), "Desktop")
            path = os.path.join(desk if os.path.exists(desk) else ".",
                                f"RPL_Screenshot_{ts}.png")
            img.save(path)
            self._log(f"  📷 Screenshot saved: {path}", "ok")
            messagebox.showinfo("Saved", f"Screenshot saved:\n{path}")
        except ImportError:
            ts   = datetime.now().strftime("%Y%m%d_%H%M%S")
            desk = os.path.join(os.path.expanduser("~"), "Desktop")
            path = os.path.join(desk if os.path.exists(desk) else ".",
                                f"RPL_Screenshot_{ts}.ps")
            self.canvas.postscript(file=path, colormode='color')
            self._log(f"  📷 Saved as PostScript: {path}", "ok")
            self._log("  ℹ  For PNG install: pip install Pillow", "dim")
            messagebox.showinfo("Saved",
                f"Saved (PostScript):\n{path}\n\n"
                "For PNG: pip install Pillow")

    # ═════════════════════════════════════════════════════════════
    #  LOG / INSPECTOR / STATS
    # ═════════════════════════════════════════════════════════════
    def _log(self, text, tag="info"):
        def _do():
            self.log_box.config(state="normal")
            self.log_box.insert("end", text + "\n", tag)
            self.log_box.see("end")
            self.log_box.config(state="disabled")
        self.root.after(0, _do)

    def _clear_log(self):
        self.log_box.config(state="normal")
        self.log_box.delete("1.0", "end")
        self.log_box.config(state="disabled")

    def _inspect(self, n):
        self.inspector.config(state="normal")
        self.inspector.delete("1.0", "end")

        def row(k, v, vtag="val"):
            self.inspector.insert("end", f"  {k:<15}", "key")
            self.inspector.insert("end", f"{v}\n", vtag)

        kind  = "SINK (Root Node)" if n.is_sink else "Sensor Node"
        par   = "ROOT" if n.is_sink else (f"Node {n.parent.id}" if n.parent else "None")
        kids  = ", ".join(f"N{c.id}" for c in n.children) or "None"
        nbs   = ", ".join(f"N{nb.id}" for nb, _ in n.neighbors) or "None"
        en    = "∞ Wired" if n.energy == float('inf') else f"{n.energy:.1f}%"
        etag  = ("teal" if (n.energy == float('inf') or n.energy > 60)
                 else "amber" if n.energy > 25 else "red")
        d2s   = ("0 px" if n.is_sink
                 else f"{n.dist_to(self.engine.sink):.1f} px"
                 if self.engine.sink else "N/A")
        if n.is_sink:
            d2p = "— (Root)"
        elif n.parent:
            d2p = f"{n.dist_to(n.parent):.1f} px  (→ N{n.parent.id})"
        elif self.engine.sink:
            d2p = "—"
        else:
            d2p = "—"
        lc_p  = f"{n.link_cost(n.parent):.4f}" if n.parent else "—"

        row("Node ID  :",  str(n.id),   "hi")
        row("Type     :",  kind,         "blue")
        row("Status   :",  "✓ Alive" if n.alive else "✗ Dead",
            "teal" if n.alive else "red")
        row("DODAG    :",  "✓ Joined" if n.dodag_joined else "○ Not Joined",
            "teal" if n.dodag_joined else "val")
        row("Rank     :",  n.rank_str,  "amber")
        row("Dist→Par :", d2p,          "amber")
        row("Energy   :",  en,           etag)
        row("Parent   :",  par,          "blue")
        row("LinkCost→:",  lc_p,        "amber")
        row("Children :",  kids,         "teal")
        row("Neighbors:", nbs,           "val")
        row("Position :",  f"({n.x:.0f}, {n.y:.0f})", "val")
        self.inspector.config(state="disabled")

    def _update_stats(self):
        for msg, lbl in self._stat_lbl.items():
            lbl.config(text=str(self.engine.stats[msg]))

    def _set_status(self, txt, color=None):
        self.status_lbl.config(text=f"●  {txt}",
                                fg=color or C["t_sec"])


# ══════════════════════════════════════════════════════════════════
if __name__ == "__main__":
    root = tk.Tk()
    try:
        from ctypes import windll
        windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass
    App(root)
    root.mainloop()
