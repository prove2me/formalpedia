-- Prove2me | solution 1 for MetricTSPSublinear.mst_estimator_program
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:39:42.571436+00:00
-- url     : https://prove2.me/submissions/d2e519cd-cf40-454f-94b4-442b5b1ce7bf

import Definitions.Def_SublinearSteiner_Machine
import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_mstWeight
import Definitions.Def_MetricTSPSublinear_cutLP
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_graph_cost
import Theorems.Thm_MetricTSPSublinear_claim_3_2
import Theorems.Thm_MetricTSPSublinear_claim_3_3

section

/-! Framework for verifying straight-line code and loops of the `SublinearSteiner` machine. -/

open scoped Classical

namespace MTSPEst
open SublinearSteiner SmaleNinth

/-- `X` sits in `Q` at position `b`. -/
def Emb (Q : Program) (b : ℕ) (X : Program) : Prop := ∀ i < X.length, Q[b + i]? = X[i]?

lemma emb_left {Q X Y : Program} {b : ℕ} (h : Emb Q b (X ++ Y)) : Emb Q b X := by
  intro i hi
  rw [h i (by simp; omega), List.getElem?_append_left hi]

lemma emb_right {Q X Y : Program} {b : ℕ} (h : Emb Q b (X ++ Y)) : Emb Q (b + X.length) Y := by
  intro i hi
  rw [Nat.add_assoc, h (X.length + i) (by simp; omega), List.getElem?_append_right (by omega)]
  simp

lemma emb_self (Q : Program) : Emb Q 0 Q := by intro i _; simp

lemma emb_at {Q X : Program} {b : ℕ} (h : Emb Q b X) (i : ℕ) (hi : i < X.length) :
    Q[b + i]? = X[i]? := h i hi

lemma emb_at0 {Q X : Program} {b : ℕ} (h : Emb Q b X) (hX : 0 < X.length) :
    Q[b]? = X[0]? := by simpa using h 0 hX

lemma emb_split {Q X Y : Program} {b b' : ℕ} (h : Emb Q b (X ++ Y)) (hb : b + X.length = b') :
    Emb Q b X ∧ Emb Q b' Y := ⟨emb_left h, hb ▸ emb_right h⟩

section reach
variable (Q : Program) {n : ℕ} (d : Fin n → Fin n → ℝ) (f : ℕ → Bool)

/-- Within `B` steps from `S` a state satisfying `P` is reached. -/
def Reach (B : ℕ) (S : State) (P : State → Prop) : Prop := ∃ T ≤ B, P ((step Q d f)^[T] S)

variable {Q d f}

lemma reach_now {B : ℕ} {S : State} {P : State → Prop} (h : P S) : Reach Q d f B S P :=
  ⟨0, Nat.zero_le _, h⟩

lemma reach_mono {B B' : ℕ} {S : State} {P P' : State → Prop} (hB : B ≤ B')
    (hP : ∀ S, P S → P' S) (h : Reach Q d f B S P) : Reach Q d f B' S P' := by
  obtain ⟨T, hT, hS⟩ := h
  exact ⟨T, hT.trans hB, hP _ hS⟩

lemma reach_bind {B1 B2 : ℕ} {S : State} {P1 P2 : State → Prop} (h1 : Reach Q d f B1 S P1)
    (h2 : ∀ S', P1 S' → Reach Q d f B2 S' P2) : Reach Q d f (B1 + B2) S P2 := by
  obtain ⟨T1, hT1, hS1⟩ := h1
  obtain ⟨T2, hT2, hS2⟩ := h2 _ hS1
  refine ⟨T2 + T1, by omega, ?_⟩
  rw [Function.iterate_add_apply]; exact hS2

lemma reach_iter (k : ℕ) {B : ℕ} {S : State} {P : State → Prop}
    (h : Reach Q d f B ((step Q d f)^[k] S) P) : Reach Q d f (k + B) S P := by
  obtain ⟨T, hT, hS⟩ := h
  refine ⟨T + k, by omega, ?_⟩
  rw [Function.iterate_add_apply]; exact hS

lemma reach_exact (k : ℕ) {S : State} {P : State → Prop} (h : P ((step Q d f)^[k] S)) :
    Reach Q d f k S P := ⟨k, le_rfl, h⟩

lemma reach_of_iter {B : ℕ} {S S' : State} {P : State → Prop} (T : ℕ) (hT : T ≤ B)
    (hS : (step Q d f)^[T] S = S') (hP : P S') : Reach Q d f B S P := ⟨T, hT, hS ▸ hP⟩

lemma iter_trans {a b : ℕ} {S S1 S2 : State} (h1 : (step Q d f)^[a] S = S1)
    (h2 : (step Q d f)^[b] S1 = S2) : (step Q d f)^[b + a] S = S2 := by
  rw [Function.iterate_add_apply, h1, h2]

/-- Generic loop: `N` iterations, each within `c` steps. -/
lemma reach_loop {Inv : ℕ → State → Prop} {c : ℕ} (N : ℕ)
    (hstep : ∀ i < N, ∀ S, Inv i S → Reach Q d f c S (Inv (i + 1))) :
    ∀ S, Inv 0 S → Reach Q d f (N * c) S (Inv N) := by
  intro S h0
  have : ∀ i ≤ N, Reach Q d f (i * c) S (Inv i) := by
    intro i
    induction i with
    | zero => intro _; exact reach_now (by simpa using h0)
    | succ i ih =>
      intro hi
      have := reach_bind (ih (by omega)) (fun S' h' => hstep i (by omega) S' h')
      simpa [Nat.succ_mul] using this
  exact this N le_rfl

/-- Loop followed by an exit. -/
lemma reach_loop_exit {Inv : ℕ → State → Prop} {c e : ℕ} (N : ℕ) {P : State → Prop}
    (hstep : ∀ i < N, ∀ S, Inv i S → Reach Q d f c S (Inv (i + 1)))
    (hexit : ∀ S, Inv N S → Reach Q d f e S P) :
    ∀ S, Inv 0 S → Reach Q d f (N * c + e) S P :=
  fun S h0 => reach_bind (reach_loop N hstep S h0) hexit

end reach

/-- Frame: `S` agrees with `S0` except on pointers `ps` and registers `rs`; memories, coins and
queries unchanged; not halted. -/
structure Fr (S0 S : State) (ps rs : List ℕ) : Prop where
  out : S.output = none
  ptrs : ∀ j, j ∉ ps → S.cfg.ptrs j = S0.cfg.ptrs j
  regs : ∀ j, j ∉ rs → S.cfg.regs j = S0.cfg.regs j
  mem : S.cfg.mem = S0.cfg.mem
  imem : S.imem = S0.imem
  coins : S.coins = S0.coins
  queries : S.queries = S0.queries

lemma Fr.refl {S : State} (ho : S.output = none) (ps rs : List ℕ) : Fr S S ps rs :=
  ⟨ho, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

lemma Fr.trans {S0 S1 S2 : State} {ps rs ps' rs' : List ℕ} (h1 : Fr S0 S1 ps rs)
    (h2 : Fr S1 S2 ps' rs') : Fr S0 S2 (ps ++ ps') (rs ++ rs') :=
  ⟨h2.out, fun j hj => by
      simp only [List.mem_append, not_or] at hj
      rw [h2.ptrs j hj.2, h1.ptrs j hj.1],
    fun j hj => by
      simp only [List.mem_append, not_or] at hj
      rw [h2.regs j hj.2, h1.regs j hj.1],
    h2.mem.trans h1.mem, h2.imem.trans h1.imem, h2.coins.trans h1.coins,
    h2.queries.trans h1.queries⟩

lemma Fr.mono {S0 S : State} {ps rs ps' rs' : List ℕ} (h : Fr S0 S ps rs)
    (hp : ∀ j ∈ ps, j ∈ ps') (hr : ∀ j ∈ rs, j ∈ rs') : Fr S0 S ps' rs' :=
  ⟨h.out, fun j hj => h.ptrs j (fun h' => hj (hp j h')),
    fun j hj => h.regs j (fun h' => hj (hr j h')), h.mem, h.imem, h.coins, h.queries⟩

lemma Fr.next {S0 S S' : State} {ps rs : List ℕ} (hF : Fr S0 S ps rs)
    (ho : S'.output = none) (hp : ∀ j, j ∉ ps → S'.cfg.ptrs j = S.cfg.ptrs j)
    (hr : ∀ j, j ∉ rs → S'.cfg.regs j = S.cfg.regs j) (hm : S'.cfg.mem = S.cfg.mem)
    (hi : S'.imem = S.imem) (hc : S'.coins = S.coins) (hq : S'.queries = S.queries) :
    Fr S0 S' ps rs :=
  ⟨ho, fun j hj => (hp j hj).trans (hF.ptrs j hj), fun j hj => (hr j hj).trans (hF.regs j hj),
    hm.trans hF.mem, hi.trans hF.imem, hc.trans hF.coins, hq.trans hF.queries⟩

/-- Frame for an explicit successor state. -/
lemma Fr.mk' {S0 S : State} {ps rs : List ℕ} (hF : Fr S0 S ps rs) (pc : ℕ) (regs : ℕ → ℝ)
    (ptrs : ℕ → ℤ) (w : ℕ)
    (hp : ∀ j, j ∉ ps → ptrs j = S.cfg.ptrs j) (hr : ∀ j, j ∉ rs → regs j = S.cfg.regs j) :
    Fr S0 ⟨⟨pc, regs, ptrs, S.cfg.mem⟩, S.imem, S.coins, w, S.queries, none⟩ ps rs :=
  hF.next rfl hp hr rfl rfl rfl rfl

lemma fr_iff {S0 S : State} {ps rs : List ℕ} (hF : Fr S0 S ps rs) (pc : ℕ) (regs : ℕ → ℝ)
    (ptrs : ℕ → ℤ) (w : ℕ) :
    Fr S0 ⟨⟨pc, regs, ptrs, S.cfg.mem⟩, S.imem, S.coins, w, S.queries, none⟩ ps rs ↔
      ((∀ j, j ∉ ps → ptrs j = S.cfg.ptrs j) ∧ (∀ j, j ∉ rs → regs j = S.cfg.regs j)) :=
  ⟨fun h => ⟨fun j hj => (h.ptrs j hj).trans (hF.ptrs j hj).symm,
    fun j hj => (h.regs j hj).trans (hF.regs j hj).symm⟩, fun h => hF.mk' _ _ _ _ h.1 h.2⟩

lemma upd_ne {α : Type} (g : ℕ → α) (a : ℕ) (v : α) (j : ℕ) (h : j ≠ a) :
    Function.update g a v j = g j := Function.update_of_ne h v g


section steps
variable {Q : Program} {n : ℕ} {d : Fin n → Fin n → ℝ} {f : ℕ → Bool}

lemma step_halted (S : State) (z : ℝ) (h : S.output = some z) : step Q d f S = S := by
  simp [step, h]

lemma iterate_halted (S : State) (z : ℝ) (h : S.output = some z) (t : ℕ) :
    (step Q d f)^[t] S = S :=
  Function.iterate_fixed (step_halted S z h) t

lemma step_coins_mono (S : State) : S.coins ≤ (step Q d f S).coins := by
  unfold step
  split
  · simp
  · split <;> simp [State.next]

end steps

end MTSPEst

end

section

/-!
Mathematical specification of the greedy growth used by the MST estimator.

`grun d mode mask start j` runs `j` steps of greedy growth on the points `u` with `mask u = true`:
the selected set starts as `{start}` with `key x = d x start`; each step picks, among unselected
masked points, one with minimal (`mode = false`, Prim) or maximal (`mode = true`, farthest-first)
key, the smallest index among ties; it records `(u, key u)`, adds `u`, and sets
`key x := min (key x) (d x u)`.
-/

open scoped Classical

namespace MTSPMst
open Finset

variable {n : ℕ}

structure GState (n : ℕ) where
  S : Finset (Fin n)
  key : Fin n → ℝ

def cands (mask : Fin n → Bool) (g : GState n) : Finset (Fin n) :=
  univ.filter (fun u => mask u = true ∧ u ∉ g.S)

/-- The optimal key value among the candidates. -/
noncomputable def bestKey (mode : Bool) (mask : Fin n → Bool) (g : GState n)
    (h : (cands mask g).Nonempty) : ℝ :=
  if mode then ((cands mask g).image g.key).max' (h.image _)
  else ((cands mask g).image g.key).min' (h.image _)

lemma bestKey_mem (mode : Bool) (mask : Fin n → Bool) (g : GState n) (h : (cands mask g).Nonempty) :
    ((cands mask g).filter (fun u => g.key u = bestKey mode mask g h)).Nonempty := by
  unfold bestKey
  split_ifs
  · obtain ⟨u, hu, hk⟩ := Finset.mem_image.mp (Finset.max'_mem _ (h.image g.key))
    exact ⟨u, Finset.mem_filter.mpr ⟨hu, hk⟩⟩
  · obtain ⟨u, hu, hk⟩ := Finset.mem_image.mp (Finset.min'_mem _ (h.image g.key))
    exact ⟨u, Finset.mem_filter.mpr ⟨hu, hk⟩⟩

/-- The selected point: smallest index among the optimal candidates. -/
noncomputable def pick (mode : Bool) (mask : Fin n → Bool) (g : GState n)
    (h : (cands mask g).Nonempty) : Fin n :=
  ((cands mask g).filter (fun u => g.key u = bestKey mode mask g h)).min' (bestKey_mem mode mask g h)

/-- One step: the recorded pair (if any) and the new state. -/
noncomputable def gstep (d : Fin n → Fin n → ℝ) (mode : Bool) (mask : Fin n → Bool) (g : GState n) :
    Option (Fin n × ℝ) × GState n :=
  if h : (cands mask g).Nonempty then
    (some (pick mode mask g h, g.key (pick mode mask g h)),
      ⟨insert (pick mode mask g h) g.S, fun x => min (g.key x) (d x (pick mode mask g h))⟩)
  else (none, g)

noncomputable def ginit (d : Fin n → Fin n → ℝ) (start : Fin n) : GState n :=
  ⟨{start}, fun x => d x start⟩

/-- `j` steps of greedy growth: final state and the list of recorded pairs. -/
noncomputable def grun (d : Fin n → Fin n → ℝ) (mode : Bool) (mask : Fin n → Bool) (start : Fin n) :
    ℕ → GState n × List (Fin n × ℝ)
  | 0 => (ginit d start, [])
  | j + 1 =>
    let r := grun d mode mask start j
    match gstep d mode mask r.1 with
    | (some p, g') => (g', r.2 ++ [p])
    | (none, g') => (g', r.2)

/-- Threshold graph on a point set `Q`: `u ~ v` iff both in `Q`, `u ≠ v`, `d u v ≤ t`. -/
def thrGraph (d : Fin n → Fin n → ℝ) (Q : Finset (Fin n)) (t : ℝ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v => u ∈ Q ∧ v ∈ Q ∧ d u v ≤ t)

/-- Number of connected components of the threshold graph on `Q`. -/
noncomputable def compCount (d : Fin n → Fin n → ℝ) (Q : Finset (Fin n)) (t : ℝ) : ℕ :=
  (Q.image (fun v => (thrGraph d Q t).connectedComponentMk v)).card

/-- Size of the component of `v` in the threshold graph on `Q`. -/
noncomputable def compSize (d : Fin n → Fin n → ℝ) (Q : Finset (Fin n)) (t : ℝ) (v : Fin n) : ℕ :=
  (Q.filter (fun u => (thrGraph d Q t).Reachable v u)).card

/-- Prefix maxima of a list of reals, `b 0 = 0`, `b j = max of the first j entries`. -/
noncomputable def pmax (L : List ℝ) (j : ℕ) : ℝ := ((L.take j).foldl max 0)

end MTSPMst

end

section

/-! Code of the greedy-growth subroutine (Prim / farthest-first) and instruction fetch lemmas. -/

open scoped Classical

namespace MTSPGrow
open SublinearSteiner

/-- The mask read from integer memory: point `u` is masked iff `I[MB + u] ≠ 0`. -/
def maskOf {n : ℕ} (St : State) (MB : ℤ) : Fin n → Bool := fun u => decide (St.imem (MB + u) ≠ 0)

/-- Greedy growth. Pointers: 100 n, 101 start, 102 K, 103 MB, 104 FB, 105 KB, 106 OV, 107 OW,
108 count, 110 loop variable, 111 address, 112 loaded value, 113 best index, 114 found flag,
115 = 0, 116 = 1. Real registers: 100 key, 101 best key, 102 difference, 103 distance. -/
def growCode (mode : Bool) (base : ℕ) : Program :=
  [ .core (.pset 115 0),  -- 0
    .core (.pset 116 1),  -- 1
    .core (.pset 110 0),  -- 2
    .core (.pjle 100 110 (base + 11)),  -- 3
    .query 103 110 101,  -- 4
    .pointerAdd 111 105 110,  -- 5
    .core (.store 111 103),  -- 6
    .pointerAdd 111 104 110,  -- 7
    .integerStore 111 115,  -- 8
    .core (.pinc 110),  -- 9
    .core (.pjle 110 110 (base + 3)),  -- 10
    .pointerAdd 111 104 101,  -- 11
    .integerStore 111 116,  -- 12
    .core (.pset 108 0),  -- 13
    .core (.pjle 102 108 (base + 55)),  -- 14
    .core (.pset 114 0),  -- 15
    .core (.pset 110 0),  -- 16
    .core (.pjle 100 110 (base + 36)),  -- 17
    .pointerAdd 111 103 110,  -- 18
    .integerLoad 112 111,  -- 19
    .core (.pjle 112 115 (base + 22)),  -- 20
    .core (.pjle 110 110 (base + 23)),  -- 21
    .core (.pjle 115 112 (base + 34)),  -- 22
    .pointerAdd 111 104 110,  -- 23
    .integerLoad 112 111,  -- 24
    .core (.pjle 116 112 (base + 34)),  -- 25
    .pointerAdd 111 105 110,  -- 26
    .core (.load 100 111),  -- 27
    .core (.pjle 114 115 (base + 31)),  -- 28
    .core (.sub 102 (if mode then 100 else 101) (if mode then 101 else 100)),  -- 29
    .core (.jle 102 (base + 34)),  -- 30
    .core (.load 101 111),  -- 31
    .core (.pcopy 113 110),  -- 32
    .core (.pset 114 1),  -- 33
    .core (.pinc 110),  -- 34
    .core (.pjle 110 110 (base + 17)),  -- 35
    .core (.pjle 114 115 (base + 55)),  -- 36
    .pointerAdd 111 106 108,  -- 37
    .integerStore 111 113,  -- 38
    .pointerAdd 111 107 108,  -- 39
    .core (.store 111 101),  -- 40
    .pointerAdd 111 104 113,  -- 41
    .integerStore 111 116,  -- 42
    .core (.pinc 108),  -- 43
    .core (.pset 110 0),  -- 44
    .core (.pjle 100 110 (base + 54)),  -- 45
    .query 103 110 113,  -- 46
    .pointerAdd 111 105 110,  -- 47
    .core (.load 100 111),  -- 48
    .core (.sub 102 100 103),  -- 49
    .core (.jle 102 (base + 52)),  -- 50
    .core (.store 111 103),  -- 51
    .core (.pinc 110),  -- 52
    .core (.pjle 110 110 (base + 45)),  -- 53
    .core (.pjle 110 110 (base + 14)) ]  -- 54

lemma growCode_length (mode : Bool) (base : ℕ) : (growCode mode base).length = 55 := rfl

theorem growCode_adm (mode : Bool) (base : ℕ) : Admissible (growCode mode base) := by
  intro i hi
  simp only [growCode, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

/-- The code is placed at `base` in `Q`. -/
def Placed (mode : Bool) (base : ℕ) (Q : Program) : Prop :=
  ∀ i < 55, Q[base + i]? = (growCode mode base)[i]?

section fetch
variable {mode : Bool} {base : ℕ} {Q : Program}
lemma q0 (h : Placed mode base Q) : Q[base + 0]? = some (.core (.pset 115 0)) := h 0 (by norm_num)
lemma q1 (h : Placed mode base Q) : Q[base + 1]? = some (.core (.pset 116 1)) := h 1 (by norm_num)
lemma q2 (h : Placed mode base Q) : Q[base + 2]? = some (.core (.pset 110 0)) := h 2 (by norm_num)
lemma q3 (h : Placed mode base Q) : Q[base + 3]? = some (.core (.pjle 100 110 (base + 11))) := h 3 (by norm_num)
lemma q4 (h : Placed mode base Q) : Q[base + 4]? = some (.query 103 110 101) := h 4 (by norm_num)
lemma q5 (h : Placed mode base Q) : Q[base + 5]? = some (.pointerAdd 111 105 110) := h 5 (by norm_num)
lemma q6 (h : Placed mode base Q) : Q[base + 6]? = some (.core (.store 111 103)) := h 6 (by norm_num)
lemma q7 (h : Placed mode base Q) : Q[base + 7]? = some (.pointerAdd 111 104 110) := h 7 (by norm_num)
lemma q8 (h : Placed mode base Q) : Q[base + 8]? = some (.integerStore 111 115) := h 8 (by norm_num)
lemma q9 (h : Placed mode base Q) : Q[base + 9]? = some (.core (.pinc 110)) := h 9 (by norm_num)
lemma q10 (h : Placed mode base Q) : Q[base + 10]? = some (.core (.pjle 110 110 (base + 3))) := h 10 (by norm_num)
lemma q11 (h : Placed mode base Q) : Q[base + 11]? = some (.pointerAdd 111 104 101) := h 11 (by norm_num)
lemma q12 (h : Placed mode base Q) : Q[base + 12]? = some (.integerStore 111 116) := h 12 (by norm_num)
lemma q13 (h : Placed mode base Q) : Q[base + 13]? = some (.core (.pset 108 0)) := h 13 (by norm_num)
lemma q14 (h : Placed mode base Q) : Q[base + 14]? = some (.core (.pjle 102 108 (base + 55))) := h 14 (by norm_num)
lemma q15 (h : Placed mode base Q) : Q[base + 15]? = some (.core (.pset 114 0)) := h 15 (by norm_num)
lemma q16 (h : Placed mode base Q) : Q[base + 16]? = some (.core (.pset 110 0)) := h 16 (by norm_num)
lemma q17 (h : Placed mode base Q) : Q[base + 17]? = some (.core (.pjle 100 110 (base + 36))) := h 17 (by norm_num)
lemma q18 (h : Placed mode base Q) : Q[base + 18]? = some (.pointerAdd 111 103 110) := h 18 (by norm_num)
lemma q19 (h : Placed mode base Q) : Q[base + 19]? = some (.integerLoad 112 111) := h 19 (by norm_num)
lemma q20 (h : Placed mode base Q) : Q[base + 20]? = some (.core (.pjle 112 115 (base + 22))) := h 20 (by norm_num)
lemma q21 (h : Placed mode base Q) : Q[base + 21]? = some (.core (.pjle 110 110 (base + 23))) := h 21 (by norm_num)
lemma q22 (h : Placed mode base Q) : Q[base + 22]? = some (.core (.pjle 115 112 (base + 34))) := h 22 (by norm_num)
lemma q23 (h : Placed mode base Q) : Q[base + 23]? = some (.pointerAdd 111 104 110) := h 23 (by norm_num)
lemma q24 (h : Placed mode base Q) : Q[base + 24]? = some (.integerLoad 112 111) := h 24 (by norm_num)
lemma q25 (h : Placed mode base Q) : Q[base + 25]? = some (.core (.pjle 116 112 (base + 34))) := h 25 (by norm_num)
lemma q26 (h : Placed mode base Q) : Q[base + 26]? = some (.pointerAdd 111 105 110) := h 26 (by norm_num)
lemma q27 (h : Placed mode base Q) : Q[base + 27]? = some (.core (.load 100 111)) := h 27 (by norm_num)
lemma q28 (h : Placed mode base Q) : Q[base + 28]? = some (.core (.pjle 114 115 (base + 31))) := h 28 (by norm_num)
lemma q29 (h : Placed mode base Q) : Q[base + 29]? = some (.core (.sub 102 (if mode then 100 else 101) (if mode then 101 else 100))) := h 29 (by norm_num)
lemma q30 (h : Placed mode base Q) : Q[base + 30]? = some (.core (.jle 102 (base + 34))) := h 30 (by norm_num)
lemma q31 (h : Placed mode base Q) : Q[base + 31]? = some (.core (.load 101 111)) := h 31 (by norm_num)
lemma q32 (h : Placed mode base Q) : Q[base + 32]? = some (.core (.pcopy 113 110)) := h 32 (by norm_num)
lemma q33 (h : Placed mode base Q) : Q[base + 33]? = some (.core (.pset 114 1)) := h 33 (by norm_num)
lemma q34 (h : Placed mode base Q) : Q[base + 34]? = some (.core (.pinc 110)) := h 34 (by norm_num)
lemma q35 (h : Placed mode base Q) : Q[base + 35]? = some (.core (.pjle 110 110 (base + 17))) := h 35 (by norm_num)
lemma q36 (h : Placed mode base Q) : Q[base + 36]? = some (.core (.pjle 114 115 (base + 55))) := h 36 (by norm_num)
lemma q37 (h : Placed mode base Q) : Q[base + 37]? = some (.pointerAdd 111 106 108) := h 37 (by norm_num)
lemma q38 (h : Placed mode base Q) : Q[base + 38]? = some (.integerStore 111 113) := h 38 (by norm_num)
lemma q39 (h : Placed mode base Q) : Q[base + 39]? = some (.pointerAdd 111 107 108) := h 39 (by norm_num)
lemma q40 (h : Placed mode base Q) : Q[base + 40]? = some (.core (.store 111 101)) := h 40 (by norm_num)
lemma q41 (h : Placed mode base Q) : Q[base + 41]? = some (.pointerAdd 111 104 113) := h 41 (by norm_num)
lemma q42 (h : Placed mode base Q) : Q[base + 42]? = some (.integerStore 111 116) := h 42 (by norm_num)
lemma q43 (h : Placed mode base Q) : Q[base + 43]? = some (.core (.pinc 108)) := h 43 (by norm_num)
lemma q44 (h : Placed mode base Q) : Q[base + 44]? = some (.core (.pset 110 0)) := h 44 (by norm_num)
lemma q45 (h : Placed mode base Q) : Q[base + 45]? = some (.core (.pjle 100 110 (base + 54))) := h 45 (by norm_num)
lemma q46 (h : Placed mode base Q) : Q[base + 46]? = some (.query 103 110 113) := h 46 (by norm_num)
lemma q47 (h : Placed mode base Q) : Q[base + 47]? = some (.pointerAdd 111 105 110) := h 47 (by norm_num)
lemma q48 (h : Placed mode base Q) : Q[base + 48]? = some (.core (.load 100 111)) := h 48 (by norm_num)
lemma q49 (h : Placed mode base Q) : Q[base + 49]? = some (.core (.sub 102 100 103)) := h 49 (by norm_num)
lemma q50 (h : Placed mode base Q) : Q[base + 50]? = some (.core (.jle 102 (base + 52))) := h 50 (by norm_num)
lemma q51 (h : Placed mode base Q) : Q[base + 51]? = some (.core (.store 111 103)) := h 51 (by norm_num)
lemma q52 (h : Placed mode base Q) : Q[base + 52]? = some (.core (.pinc 110)) := h 52 (by norm_num)
lemma q53 (h : Placed mode base Q) : Q[base + 53]? = some (.core (.pjle 110 110 (base + 45))) := h 53 (by norm_num)
lemma q54 (h : Placed mode base Q) : Q[base + 54]? = some (.core (.pjle 110 110 (base + 14))) := h 54 (by norm_num)

end fetch
end MTSPGrow

end

section

/-! Combinatorial lemmas about `MTSPMst.pick` / `grun` used by the verification of `growCode`. -/

open scoped Classical

namespace MTSPGrow
open MTSPMst Finset

variable {n : ℕ}

/-- `a` is at least as good as `b` (`mode = false`: smaller, `mode = true`: larger). -/
def bt (mode : Bool) (a b : ℝ) : Prop := if mode then b ≤ a else a ≤ b

/-- `b` is the optimum of `A` with ties broken towards the smallest index. -/
def IsBest (mode : Bool) (key : Fin n → ℝ) (A : Finset (Fin n)) (b : Fin n) : Prop :=
  b ∈ A ∧ ∀ v ∈ A, bt mode (key b) (key v) ∧ (key v = key b → b ≤ v)

lemma bestKey_eq (mode : Bool) (mask : Fin n → Bool) (g : GState n) (h : (cands mask g).Nonempty)
    (b : Fin n) (hb : IsBest mode g.key (cands mask g) b) : bestKey mode mask g h = g.key b := by
  unfold bestKey
  cases mode
  · simp only [Bool.false_eq_true, if_false]
    apply le_antisymm (min'_le _ _ (mem_image_of_mem _ hb.1))
    apply le_min'
    intro y hy
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hy
    have := (hb.2 v hv).1
    simpa [bt] using this
  · simp only [if_true]
    apply le_antisymm _ (le_max' _ _ (mem_image_of_mem _ hb.1))
    apply max'_le
    intro y hy
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hy
    have := (hb.2 v hv).1
    simpa [bt] using this

lemma pick_eq (mode : Bool) (mask : Fin n → Bool) (g : GState n) (h : (cands mask g).Nonempty)
    (b : Fin n) (hb : IsBest mode g.key (cands mask g) b) : pick mode mask g h = b := by
  unfold pick
  have hk := bestKey_eq mode mask g h b hb
  apply le_antisymm
  · apply min'_le
    rw [mem_filter, hk]
    exact ⟨hb.1, rfl⟩
  · apply le_min'
    intro v hv
    rw [mem_filter, hk] at hv
    exact (hb.2 v hv.1).2 hv.2

/-- Candidates with index `< u`. -/
def candsLt (mask : Fin n → Bool) (g : GState n) (u : ℕ) : Finset (Fin n) :=
  (cands mask g).filter (fun v => (v : ℕ) < u)

lemma candsLt_zero (mask : Fin n → Bool) (g : GState n) : candsLt mask g 0 = ∅ := by
  ext v; simp [candsLt]

lemma candsLt_n (mask : Fin n → Bool) (g : GState n) : candsLt mask g n = cands mask g := by
  ext v; simp [candsLt]

lemma mem_cands (mask : Fin n → Bool) (g : GState n) (v : Fin n) :
    v ∈ cands mask g ↔ mask v = true ∧ v ∉ g.S := by
  simp [cands]

lemma candsLt_succ_not (mask : Fin n → Bool) (g : GState n) (u : ℕ) (hu : u < n)
    (hc : (⟨u, hu⟩ : Fin n) ∉ cands mask g) : candsLt mask g (u + 1) = candsLt mask g u := by
  ext v
  simp only [candsLt, mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h | h
    · exact h
    · exfalso; apply hc; have : v = ⟨u, hu⟩ := Fin.ext h
      rw [← this]; exact h1
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

lemma candsLt_succ_mem (mask : Fin n → Bool) (g : GState n) (u : ℕ) (hu : u < n) (v : Fin n) :
    v ∈ candsLt mask g (u + 1) ↔ v ∈ candsLt mask g u ∨ (v = ⟨u, hu⟩ ∧ v ∈ cands mask g) := by
  simp only [candsLt, mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨Fin.ext h, h1⟩
  · rintro (⟨h1, h2⟩ | ⟨rfl, h1⟩)
    · exact ⟨h1, by omega⟩
    · exact ⟨h1, by simp⟩

lemma lt_of_mem_candsLt {mask : Fin n → Bool} {g : GState n} {u : ℕ} {v : Fin n}
    (h : v ∈ candsLt mask g u) : (v : ℕ) < u := (mem_filter.1 h).2

lemma isBest_first (mode : Bool) (mask : Fin n → Bool) (g : GState n) (u : ℕ) (hu : u < n)
    (h0 : candsLt mask g u = ∅) (hc : (⟨u, hu⟩ : Fin n) ∈ cands mask g) :
    IsBest mode g.key (candsLt mask g (u + 1)) ⟨u, hu⟩ := by
  have hmem : ∀ v, v ∈ candsLt mask g (u + 1) ↔ v = ⟨u, hu⟩ := by
    intro v
    rw [candsLt_succ_mem mask g u hu, h0]
    constructor
    · rintro (h | ⟨h, -⟩)
      · simp at h
      · exact h
    · rintro rfl; exact Or.inr ⟨rfl, hc⟩
  refine ⟨(hmem _).2 rfl, fun v hv => ?_⟩
  rw [(hmem v).1 hv]
  refine ⟨?_, fun _ => le_rfl⟩
  unfold bt; split_ifs <;> exact le_rfl

lemma isBest_take (mode : Bool) (mask : Fin n → Bool) (g : GState n) (u : ℕ) (hu : u < n)
    (b : Fin n) (hb : IsBest mode g.key (candsLt mask g u) b) (hc : (⟨u, hu⟩ : Fin n) ∈ cands mask g)
    (hlt : ¬ bt mode (g.key b) (g.key ⟨u, hu⟩)) :
    IsBest mode g.key (candsLt mask g (u + 1)) ⟨u, hu⟩ := by
  refine ⟨(candsLt_succ_mem mask g u hu _).2 (Or.inr ⟨rfl, hc⟩), fun v hv => ?_⟩
  rcases (candsLt_succ_mem mask g u hu _).1 hv with hv | ⟨rfl, -⟩
  · have h1 := (hb.2 v hv).1
    unfold bt at hlt h1 ⊢
    cases mode <;> simp only [Bool.false_eq_true, if_false, if_true] at hlt h1 ⊢ <;>
      refine ⟨by linarith, fun h => ?_⟩ <;> exfalso <;> linarith
  · refine ⟨?_, fun _ => le_rfl⟩
    unfold bt; split_ifs <;> exact le_rfl

lemma isBest_keep (mode : Bool) (mask : Fin n → Bool) (g : GState n) (u : ℕ) (hu : u < n)
    (b : Fin n) (hb : IsBest mode g.key (candsLt mask g u) b)
    (hle : bt mode (g.key b) (g.key ⟨u, hu⟩)) :
    IsBest mode g.key (candsLt mask g (u + 1)) b := by
  refine ⟨(candsLt_succ_mem mask g u hu _).2 (Or.inl hb.1), fun v hv => ?_⟩
  rcases (candsLt_succ_mem mask g u hu _).1 hv with hv | ⟨rfl, -⟩
  · exact hb.2 v hv
  · refine ⟨hle, fun _ => ?_⟩
    have := lt_of_mem_candsLt hb.1
    exact Fin.le_iff_val_le_val.2 (by simp; omega)

/-! ### `grun` -/

lemma grun_succ (d : Fin n → Fin n → ℝ) (mode : Bool) (mask : Fin n → Bool) (start : Fin n) (j : ℕ) :
    grun d mode mask start (j + 1) =
      match gstep d mode mask (grun d mode mask start j).1 with
      | (some p, g') => (g', (grun d mode mask start j).2 ++ [p])
      | (none, g') => (g', (grun d mode mask start j).2) := rfl

lemma grun_succ_none (d : Fin n → Fin n → ℝ) (mode : Bool) (mask : Fin n → Bool) (start : Fin n)
    (j : ℕ) (h : ¬ (cands mask (grun d mode mask start j).1).Nonempty) :
    grun d mode mask start (j + 1) = grun d mode mask start j := by
  rw [grun_succ]
  simp only [gstep, dif_neg h]

lemma grun_succ_some (d : Fin n → Fin n → ℝ) (mode : Bool) (mask : Fin n → Bool) (start : Fin n)
    (j : ℕ) (h : (cands mask (grun d mode mask start j).1).Nonempty) :
    grun d mode mask start (j + 1) =
      (⟨insert (pick mode mask _ h) (grun d mode mask start j).1.S,
        fun x => min ((grun d mode mask start j).1.key x) (d x (pick mode mask _ h))⟩,
        (grun d mode mask start j).2 ++
          [(pick mode mask _ h, (grun d mode mask start j).1.key (pick mode mask _ h))]) := by
  rw [grun_succ]
  simp only [gstep, dif_pos h]

lemma grun_stable (d : Fin n → Fin n → ℝ) (mode : Bool) (mask : Fin n → Bool) (start : Fin n)
    (j : ℕ) (h : ¬ (cands mask (grun d mode mask start j).1).Nonempty) :
    ∀ m, grun d mode mask start (j + m) = grun d mode mask start j := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← Nat.add_assoc, grun_succ_none d mode mask start (j + m) (by rw [ih]; exact h), ih]

lemma grun_length_le (d : Fin n → Fin n → ℝ) (mode : Bool) (mask : Fin n → Bool) (start : Fin n) :
    ∀ j, (grun d mode mask start j).2.length ≤ j := by
  intro j
  induction j with
  | zero => simp [grun]
  | succ j ih =>
    by_cases h : (cands mask (grun d mode mask start j).1).Nonempty
    · rw [grun_succ_some d mode mask start j h]; simp; omega
    · rw [grun_succ_none d mode mask start j h]; omega

lemma grun_zero (d : Fin n → Fin n → ℝ) (mode : Bool) (mask : Fin n → Bool) (start : Fin n) :
    grun d mode mask start 0 = (⟨{start}, fun x => d x start⟩, []) := rfl

end MTSPGrow

end

section

set_option linter.unusedSimpArgs false

open scoped Classical

namespace MTSPGrow
open SublinearSteiner SmaleNinth

lemma oracle_fin {n : ℕ} (d : Fin n → Fin n → ℝ) (u v : Fin n) :
    oracleAnswer d ((u : ℕ) : ℤ) ((v : ℕ) : ℤ) = d u v := by
  simp [oracleAnswer, toPoint]

/-! ### Bounded reachability -/

/-- Within `t` steps from `A` some state satisfies `P`. -/
def Reach (Q : Program) {n : ℕ} (d : Fin n → Fin n → ℝ) (f : ℕ → Bool) (A : State)
    (P : State → Prop) (t : ℕ) : Prop :=
  ∃ s ≤ t, P ((step Q d f)^[s] A)

section reach
variable {Q : Program} {n : ℕ} {d : Fin n → Fin n → ℝ} {f : ℕ → Bool}

lemma Reach.of_iter {A : State} {P : State → Prop} {s t : ℕ} (h : P ((step Q d f)^[s] A))
    (hs : s ≤ t) : Reach Q d f A P t := ⟨s, hs, h⟩

lemma Reach.mono {A : State} {P : State → Prop} {t t' : ℕ} (h : Reach Q d f A P t)
    (ht : t ≤ t') : Reach Q d f A P t' := by
  obtain ⟨s, hs, h⟩ := h; exact ⟨s, le_trans hs ht, h⟩

lemma Reach.imp {A : State} {P R : State → Prop} {t : ℕ} (h : Reach Q d f A P t)
    (hPR : ∀ B, P B → R B) : Reach Q d f A R t := by
  obtain ⟨s, hs, h⟩ := h; exact ⟨s, hs, hPR _ h⟩

lemma Reach.trans {A : State} {P R : State → Prop} {t1 t2 : ℕ} (h1 : Reach Q d f A P t1)
    (h2 : ∀ B, P B → Reach Q d f B R t2) : Reach Q d f A R (t1 + t2) := by
  obtain ⟨s1, hs1, hP⟩ := h1
  obtain ⟨s2, hs2, hR⟩ := h2 _ hP
  exact ⟨s2 + s1, by omega, by rwa [Function.iterate_add_apply]⟩

lemma reach_loop (Inv : ℕ → State → Prop) (c N : ℕ)
    (hstep : ∀ k < N, ∀ St, Inv k St → Reach Q d f St (Inv (k + 1)) c) :
    ∀ k ≤ N, ∀ St, Inv 0 St → Reach Q d f St (Inv k) (c * k) := by
  intro k
  induction k with
  | zero => intro _ St h; exact ⟨0, le_rfl, h⟩
  | succ k ih =>
    intro hk St h
    have := Reach.trans (ih (by omega) St h) (fun B hB => hstep k (by omega) B hB)
    rwa [show c * k + c = c * (k + 1) by ring] at this

end reach

section
variable {mode : Bool} {base : ℕ} {Q : Program} (hP : Placed mode base Q) {n : ℕ}
  (d : Fin n → Fin n → ℝ) (f : ℕ → Bool)

def IInv (base : ℕ) (A : State) (KB FB : ℤ) (start : Fin n) (d : Fin n → Fin n → ℝ) (u : ℕ)
    (St : State) : Prop :=
  St.cfg.pc = base + 3 ∧ St.output = none ∧ St.coins = A.coins ∧ St.queries = A.queries + u ∧
  St.cfg.ptrs 110 = u ∧ St.cfg.ptrs 115 = 0 ∧ St.cfg.ptrs 116 = 1 ∧
  (∀ j, j ≠ 110 → j ≠ 111 → j ≠ 115 → j ≠ 116 → St.cfg.ptrs j = A.cfg.ptrs j) ∧
  (∀ j, j ≠ 103 → St.cfg.regs j = A.cfg.regs j) ∧
  (∀ v : Fin n, (v : ℕ) < u → St.cfg.mem (KB + (v : ℕ)) = d v start) ∧
  (∀ z, ¬ (KB ≤ z ∧ z < KB + u) → St.cfg.mem z = A.cfg.mem z) ∧
  (∀ v : Fin n, (v : ℕ) < u → St.imem (FB + (v : ℕ)) = 0) ∧
  (∀ z, ¬ (FB ≤ z ∧ z < FB + u) → St.imem z = A.imem z)

include hP in
lemma init_iter (A : State) (KB FB : ℤ) (start : Fin n) (hA100 : A.cfg.ptrs 100 = n)
    (hA101 : A.cfg.ptrs 101 = (start : ℕ)) (hA104 : A.cfg.ptrs 104 = FB)
    (hA105 : A.cfg.ptrs 105 = KB) (u : ℕ) (hu : u < n) (St : State)
    (h : IInv base A KB FB start d u St) :
    IInv base A KB FB start d (u + 1) ((step Q d f)^[8] St) := by
  obtain ⟨hpc, ho, hc, hq, h110, h115, h116, hp, hr, hm1, hm2, hi1, hi2⟩ := h
  have e100 : St.cfg.ptrs 100 = n := by rw [hp 100 (by decide) (by decide) (by decide) (by decide), hA100]
  have e101 : St.cfg.ptrs 101 = (start : ℕ) := by
    rw [hp 101 (by decide) (by decide) (by decide) (by decide), hA101]
  have e104 : St.cfg.ptrs 104 = FB := by rw [hp 104 (by decide) (by decide) (by decide) (by decide), hA104]
  have e105 : St.cfg.ptrs 105 = KB := by rw [hp 105 (by decide) (by decide) (by decide) (by decide), hA105]
  have hnu : ¬ (n : ℤ) ≤ u := by omega
  have horc : oracleAnswer d (u : ℤ) ((start : ℕ) : ℤ) = d ⟨u, hu⟩ start :=
    oracle_fin d ⟨u, hu⟩ start
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp [IInv, step, ho, hpc, q3 hP, q4 hP, q5 hP, q6 hP, q7 hP, q8 hP, q9 hP, q10 hP, RAMStep,
    List.getElem?_map, State.next, Instr.coreOf, e100, e101, e104, e105, h110, h115, hnu, horc,
    hc, hq]
  refine ⟨by ring, h116, fun j h1 h2 h3 h4 => ?_, fun j hj => ?_, fun v hv => ?_, fun z hz => ?_,
    fun v hv => ?_, fun z hz => ?_⟩
  · simp [Function.update_apply, h1, h2]; exact hp j h1 h2 h3 h4
  · simp [Function.update_apply, hj]; exact hr j hj
  · rcases Nat.lt_or_eq_of_le hv with hv | hv
    · rw [Function.update_of_ne (by omega)]; exact hm1 v hv
    · have : v = ⟨u, hu⟩ := Fin.ext hv
      subst this; simp
  · rw [Function.update_of_ne (by omega)]; exact hm2 z (by omega)
  · rcases Nat.lt_or_eq_of_le hv with hv | hv
    · rw [Function.update_of_ne (by omega)]; exact hi1 v hv
    · have : v = ⟨u, hu⟩ := Fin.ext hv
      subst this; simp
  · rw [Function.update_of_ne (by omega)]; exact hi2 z (by omega)

open MTSPMst in
/-- Representation of a greedy-growth state `R` after `j` recorded steps, at the outer loop head. -/
def ORep (base : ℕ) (A : State) (n K : ℕ) (FB KB OV OW : ℤ) (R : GState n × List (Fin n × ℝ))
    (j : ℕ) (St : State) : Prop :=
  St.cfg.pc = base + 14 ∧ St.output = none ∧ St.coins = A.coins ∧
  St.queries = A.queries + n * (1 + j) ∧ St.cfg.ptrs 108 = j ∧ St.cfg.ptrs 115 = 0 ∧
  St.cfg.ptrs 116 = 1 ∧
  (∀ i, (i < 108 ∨ 140 ≤ i) → St.cfg.ptrs i = A.cfg.ptrs i) ∧
  (∀ i, (i < 100 ∨ 140 ≤ i) → St.cfg.regs i = A.cfg.regs i) ∧
  R.2.length = j ∧ j ≤ K ∧
  (∀ u : Fin n, St.cfg.mem (KB + (u : ℕ)) = R.1.key u) ∧
  (∀ u : Fin n, St.imem (FB + (u : ℕ)) = if u ∈ R.1.S then 1 else 0) ∧
  (∀ i (hi : i < R.2.length), St.imem (OV + i) = ((R.2[i]).1 : ℕ) ∧
    St.cfg.mem (OW + i) = (R.2[i]).2) ∧
  (∀ z, ¬ (FB ≤ z ∧ z < FB + n) → ¬ (OV ≤ z ∧ z < OV + K) → St.imem z = A.imem z) ∧
  (∀ z, ¬ (KB ≤ z ∧ z < KB + n) → ¬ (OW ≤ z ∧ z < OW + K) → St.cfg.mem z = A.cfg.mem z)

include hP in
lemma init_pre (A : State) (KB FB : ℤ) (start : Fin n) (hpc : A.cfg.pc = base)
    (ho : A.output = none) : IInv base A KB FB start d 0 ((step Q d f)^[3] A) := by
  have q0' : Q[base]? = some (.core (.pset 115 0)) := by simpa using q0 hP
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp [IInv, step, ho, hpc, q0', q1 hP, q2 hP, RAMStep, List.getElem?_map, State.next,
    Instr.coreOf]
  intro j h1 h2 h3 h4
  simp [h1, h3, h4]

include hP in
lemma init_post (A : State) (K : ℕ) (KB FB OV OW : ℤ) (start : Fin n) (hA100 : A.cfg.ptrs 100 = n)
    (hA101 : A.cfg.ptrs 101 = (start : ℕ)) (hA104 : A.cfg.ptrs 104 = FB)
    (St : State) (h : IInv base A KB FB start d n St) :
    ORep base A n K FB KB OV OW (MTSPMst.ginit d start, []) 0 ((step Q d f)^[4] St) := by
  obtain ⟨hpc, ho, hc, hq, h110, h115, h116, hp, hr, hm1, hm2, hi1, hi2⟩ := h
  have e100 : St.cfg.ptrs 100 = n := by rw [hp 100 (by decide) (by decide) (by decide) (by decide), hA100]
  have e101 : St.cfg.ptrs 101 = (start : ℕ) := by
    rw [hp 101 (by decide) (by decide) (by decide) (by decide), hA101]
  have e104 : St.cfg.ptrs 104 = FB := by rw [hp 104 (by decide) (by decide) (by decide) (by decide), hA104]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp [ORep, step, ho, hpc, q3 hP, q11 hP, q12 hP, q13 hP, RAMStep,
    List.getElem?_map, State.next, Instr.coreOf, e100, e101, e104, h110, h115, h116,
    hc, hq]
  refine ⟨fun i hi => ?_, fun i hi => hr i (by omega), fun u => ?_, fun u => ?_,
    fun z h1 h2 => ?_, fun z h1 h2 => hm2 z (by omega)⟩
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hp i (by omega) (by omega) (by omega) (by omega)
  · simp only [MTSPMst.ginit]; exact hm1 u u.isLt
  · simp only [MTSPMst.ginit, Finset.mem_singleton]
    by_cases hu : u = start
    · subst hu; simp
    · rw [Function.update_of_ne (fun h => hu (Fin.ext (by omega))), if_neg hu]; exact hi1 u u.isLt
  · rw [Function.update_of_ne (by have := start.isLt; omega)]; exact hi2 z (by omega)

include hP in
lemma init_run (A : State) (K : ℕ) (KB FB OV OW : ℤ) (start : Fin n) (hpc : A.cfg.pc = base)
    (ho : A.output = none) (hA100 : A.cfg.ptrs 100 = n)
    (hA101 : A.cfg.ptrs 101 = (start : ℕ)) (hA104 : A.cfg.ptrs 104 = FB)
    (hA105 : A.cfg.ptrs 105 = KB) :
    Reach Q d f A (ORep base A n K FB KB OV OW (MTSPMst.ginit d start, []) 0) (8 * n + 7) := by
  have h1 : Reach Q d f A (IInv base A KB FB start d 0) 3 :=
    Reach.of_iter (init_pre hP d f A KB FB start hpc ho) le_rfl
  have h2 := Reach.trans h1 (fun B hB => reach_loop (Q := Q) (d := d) (f := f)
    (fun k => IInv base A KB FB start d k) 8 n
    (fun k hk St h => Reach.of_iter
      (init_iter hP d f A KB FB start hA100 hA101 hA104 hA105 k hk St h) le_rfl) n le_rfl B hB)
  have h3 := Reach.trans h2 (fun B hB => Reach.of_iter (t := 4)
    (init_post hP d f A K KB FB OV OW start hA100 hA101 hA104 B hB) le_rfl)
  exact h3.mono (by ring_nf; omega)

end
end MTSPGrow

end

section

set_option linter.unusedSimpArgs false
open scoped Classical

namespace MTSPGrow
open SublinearSteiner SmaleNinth MTSPMst

section
variable {mode : Bool} {base : ℕ} {Q : Program} (hP : Placed mode base Q) {n : ℕ}
  (d : Fin n → Fin n → ℝ) (f : ℕ → Bool)

include hP in
lemma scan_mask_nz (St : State) (MB : ℤ) (u : ℕ) (hu : u < n) (hpc : St.cfg.pc = base + 17)
    (ho : St.output = none) (h100 : St.cfg.ptrs 100 = n) (h103 : St.cfg.ptrs 103 = MB)
    (h110 : St.cfg.ptrs 110 = u) (h115 : St.cfg.ptrs 115 = 0) (hm : St.imem (MB + u) ≠ 0) :
    (step Q d f)^[5] St = ⟨⟨base + 23, St.cfg.regs,
      Function.update (Function.update St.cfg.ptrs 111 (MB + u)) 112 (St.imem (MB + u)),
      St.cfg.mem⟩, St.imem, St.coins, St.work + 5, St.queries, St.output⟩ := by
  have hnu : ¬ (n : ℤ) ≤ u := by omega
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rcases lt_or_gt_of_ne hm with hneg | hpos
  · have h1 : St.imem (MB + u) ≤ 0 := hneg.le
    have h2 : ¬ 0 ≤ St.imem (MB + u) := not_le.2 hneg
    simp [step, ho, hpc, q17 hP, q18 hP, q19 hP, q20 hP, q22 hP, RAMStep,
      List.getElem?_map, State.next, Instr.coreOf, h100, h103, h110, h115, hnu, h1, h2]
  · have h1 : ¬ St.imem (MB + u) ≤ 0 := not_le.2 hpos
    simp [step, ho, hpc, q17 hP, q18 hP, q19 hP, q20 hP, q21 hP, RAMStep,
      List.getElem?_map, State.next, Instr.coreOf, h100, h103, h110, h115, hnu, h1]

/-- Scan loop invariant at pc `17`, relative to the state `B` at the start of the scan. -/
def SInv (base : ℕ) (B : State) (mode : Bool) (mask : Fin n → Bool) (g : GState n) (u : ℕ)
    (St : State) : Prop :=
  St.cfg.pc = base + 17 ∧ St.output = none ∧ St.coins = B.coins ∧ St.queries = B.queries ∧
  St.cfg.mem = B.cfg.mem ∧ St.imem = B.imem ∧
  (∀ j, (j < 110 ∨ 114 < j) → St.cfg.ptrs j = B.cfg.ptrs j) ∧
  (∀ j, (j < 100 ∨ 102 < j) → St.cfg.regs j = B.cfg.regs j) ∧
  St.cfg.ptrs 110 = u ∧ u ≤ n ∧
  ((candsLt mask g u = ∅ ∧ St.cfg.ptrs 114 = 0) ∨
    (∃ b, IsBest mode g.key (candsLt mask g u) b ∧ St.cfg.ptrs 114 = 1 ∧
      St.cfg.ptrs 113 = (b : ℕ) ∧ St.cfg.regs 101 = g.key b))

include hP in
lemma scan_iter (B : State) (mask : Fin n → Bool) (g : GState n) (MB FB KB : ℤ)
    (hB100 : B.cfg.ptrs 100 = n) (hB103 : B.cfg.ptrs 103 = MB) (hB104 : B.cfg.ptrs 104 = FB)
    (hB105 : B.cfg.ptrs 105 = KB) (hB115 : B.cfg.ptrs 115 = 0) (hB116 : B.cfg.ptrs 116 = 1)
    (hkey : ∀ v : Fin n, B.cfg.mem (KB + (v : ℕ)) = g.key v)
    (hflag : ∀ v : Fin n, B.imem (FB + (v : ℕ)) = if v ∈ g.S then 1 else 0)
    (hmask : ∀ v : Fin n, mask v = decide (B.imem (MB + (v : ℕ)) ≠ 0))
    (u : ℕ) (hu : u < n) (St : State) (h : SInv base B mode mask g u St) :
    Reach Q d f St (SInv base B mode mask g (u + 1)) 20 := by
  obtain ⟨hpc, ho, hc, hq, hmem, himem, hp, hr, h110, -, hbest⟩ := h
  have e100 : St.cfg.ptrs 100 = n := by rw [hp 100 (by omega), hB100]
  have e103 : St.cfg.ptrs 103 = MB := by rw [hp 103 (by omega), hB103]
  have e104 : St.cfg.ptrs 104 = FB := by rw [hp 104 (by omega), hB104]
  have e105 : St.cfg.ptrs 105 = KB := by rw [hp 105 (by omega), hB105]
  have e115 : St.cfg.ptrs 115 = 0 := by rw [hp 115 (by omega), hB115]
  have e116 : St.cfg.ptrs 116 = 1 := by rw [hp 116 (by omega), hB116]
  set u' : Fin n := ⟨u, hu⟩ with hu'
  have hk' : B.cfg.mem (KB + (u : ℤ)) = g.key u' := hkey u'
  have hf' : B.imem (FB + (u : ℤ)) = if u' ∈ g.S then 1 else 0 := hflag u'
  have hnu : ¬ (n : ℤ) ≤ u := by omega
  by_cases hm0 : B.imem (MB + u) = 0
  · -- not masked
    have hnc : u' ∉ cands mask g := by
      have : B.imem (MB + ((u' : ℕ) : ℤ)) = 0 := hm0
      rw [mem_cands, hmask u']; simp [this]
    have hC := candsLt_succ_not mask g u hu hnc
    refine Reach.of_iter (s := 7) ?_ (by norm_num)
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp [SInv, step, ho, hpc, q17 hP, q18 hP, q19 hP, q20 hP, q22 hP, q34 hP, q35 hP, RAMStep,
      List.getElem?_map, State.next, Instr.coreOf, e100, e103, e115, h110, hnu, himem, hm0, hc, hq,
      hmem, hC]
    refine ⟨fun j hj => ?_, hr, hu, hbest⟩
    simp only [Function.update_apply]
    split_ifs <;> first | omega | exact hp j hj
  · -- masked
    have hm1 : St.imem (MB + u) ≠ 0 := by rw [himem]; exact hm0
    have hmk : mask u' = true := by
      have : B.imem (MB + ((u' : ℕ) : ℤ)) ≠ 0 := hm0
      rw [hmask u']; simpa using this
    have hM := scan_mask_nz hP d f St MB u hu hpc ho e100 e103 h110 e115 hm1
    by_cases hS : u' ∈ g.S
    · -- already selected
      have hnc : u' ∉ cands mask g := by rw [mem_cands]; tauto
      have hC := candsLt_succ_not mask g u hu hnc
      have hfl : B.imem (FB + (u : ℤ)) = 1 := by rw [hf', if_pos hS]
      refine Reach.of_iter (s := 5 + 5) ?_ (by norm_num)
      rw [Function.iterate_add_apply, hM]
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      simp [SInv, step, ho, q23 hP, q24 hP, q25 hP, q34 hP, q35 hP, RAMStep,
        List.getElem?_map, State.next, Instr.coreOf, e104, e116, h110, himem, hfl, hc, hq,
        hmem, hC]
      refine ⟨fun j hj => ?_, hr, hu, hbest⟩
      simp only [Function.update_apply]
      split_ifs <;> first | omega | exact hp j hj
    · have hcand : u' ∈ cands mask g := by rw [mem_cands]; exact ⟨hmk, hS⟩
      have hfl : B.imem (FB + (u : ℤ)) = 0 := by rw [hf', if_neg hS]
      rcases hbest with ⟨h0, h114⟩ | ⟨b, hb, h114, h113, h101⟩
      · -- first candidate
        have hB := isBest_first mode mask g u hu h0 hcand
        refine Reach.of_iter (s := 11 + 5) ?_ (by norm_num)
        rw [Function.iterate_add_apply, hM]
        simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
        simp [SInv, step, ho, q23 hP, q24 hP, q25 hP, q26 hP, q27 hP, q28 hP, q31 hP, q32 hP,
          q33 hP, q34 hP, q35 hP, RAMStep,
          List.getElem?_map, State.next, Instr.coreOf, e104, e105, e115, e116, h110, h114, himem,
          hfl, hc, hq, hmem, hk']
        refine ⟨fun j hj => ?_, fun j hj => ?_, hu, ⟨u', hB, rfl, rfl⟩⟩
        · simp only [Function.update_apply]
          split_ifs <;> first | omega | exact hp j hj
        · simp only [Function.update_apply]
          split_ifs <;> first | omega | exact hr j hj
      · by_cases hbt : bt mode (g.key b) (g.key u')
        · -- keep
          have hB := isBest_keep mode mask g u hu b hb hbt
          refine Reach.of_iter (s := 10 + 5) ?_ (by norm_num)
          rw [Function.iterate_add_apply, hM]
          simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
          cases mode
          · have hc' : g.key b - g.key u' ≤ 0 := by simp only [bt] at hbt; simp at hbt; linarith
            simp [SInv, step, ho, q23 hP, q24 hP, q25 hP, q26 hP, q27 hP, q28 hP, q29 hP, q30 hP,
              q34 hP, q35 hP, RAMStep,
              List.getElem?_map, State.next, Instr.coreOf, e104, e105, e115, e116, h110, h114,
              himem, hfl, hc, hq, hmem, hk', h101, hc']
            refine ⟨fun j hj => ?_, fun j hj => ?_, hu, ⟨b, hB, h113, rfl⟩⟩
            · simp only [Function.update_apply]
              split_ifs <;> first | omega | exact hp j hj
            · simp only [Function.update_apply]
              split_ifs <;> first | omega | exact hr j hj
          · have hc' : g.key u' - g.key b ≤ 0 := by simp only [bt] at hbt; simp at hbt; linarith
            simp [SInv, step, ho, q23 hP, q24 hP, q25 hP, q26 hP, q27 hP, q28 hP, q29 hP, q30 hP,
              q34 hP, q35 hP, RAMStep,
              List.getElem?_map, State.next, Instr.coreOf, e104, e105, e115, e116, h110, h114,
              himem, hfl, hc, hq, hmem, hk', h101, hc']
            refine ⟨fun j hj => ?_, fun j hj => ?_, hu, ⟨b, hB, h113, rfl⟩⟩
            · simp only [Function.update_apply]
              split_ifs <;> first | omega | exact hp j hj
            · simp only [Function.update_apply]
              split_ifs <;> first | omega | exact hr j hj
        · -- take
          have hB := isBest_take mode mask g u hu b hb hcand hbt
          refine Reach.of_iter (s := 13 + 5) ?_ (by norm_num)
          rw [Function.iterate_add_apply, hM]
          simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
          cases mode
          · have hc' : ¬ g.key b - g.key u' ≤ 0 := by
              simp only [bt] at hbt; simp at hbt; intro h; linarith
            simp [SInv, step, ho, q23 hP, q24 hP, q25 hP, q26 hP, q27 hP, q28 hP, q29 hP, q30 hP,
              q31 hP, q32 hP, q33 hP, q34 hP, q35 hP, RAMStep,
              List.getElem?_map, State.next, Instr.coreOf, e104, e105, e115, e116, h110, h114,
              himem, hfl, hc, hq, hmem, hk', h101, hc']
            refine ⟨fun j hj => ?_, fun j hj => ?_, hu, ⟨u', hB, rfl, rfl⟩⟩
            · simp only [Function.update_apply]
              split_ifs <;> first | omega | exact hp j hj
            · simp only [Function.update_apply]
              split_ifs <;> first | omega | exact hr j hj
          · have hc' : ¬ g.key u' - g.key b ≤ 0 := by
              simp only [bt] at hbt; simp at hbt; intro h; linarith
            simp [SInv, step, ho, q23 hP, q24 hP, q25 hP, q26 hP, q27 hP, q28 hP, q29 hP, q30 hP,
              q31 hP, q32 hP, q33 hP, q34 hP, q35 hP, RAMStep,
              List.getElem?_map, State.next, Instr.coreOf, e104, e105, e115, e116, h110, h114,
              himem, hfl, hc, hq, hmem, hk', h101, hc']
            refine ⟨fun j hj => ?_, fun j hj => ?_, hu, ⟨u', hB, rfl, rfl⟩⟩
            · simp only [Function.update_apply]
              split_ifs <;> first | omega | exact hp j hj
            · simp only [Function.update_apply]
              split_ifs <;> first | omega | exact hr j hj

include hP in
lemma scan_run (B : State) (mask : Fin n → Bool) (g : GState n) (MB FB KB : ℤ)
    (hB100 : B.cfg.ptrs 100 = n) (hB103 : B.cfg.ptrs 103 = MB) (hB104 : B.cfg.ptrs 104 = FB)
    (hB105 : B.cfg.ptrs 105 = KB) (hB115 : B.cfg.ptrs 115 = 0) (hB116 : B.cfg.ptrs 116 = 1)
    (hkey : ∀ v : Fin n, B.cfg.mem (KB + (v : ℕ)) = g.key v)
    (hflag : ∀ v : Fin n, B.imem (FB + (v : ℕ)) = if v ∈ g.S then 1 else 0)
    (hmask : ∀ v : Fin n, mask v = decide (B.imem (MB + (v : ℕ)) ≠ 0))
    (h0 : SInv base B mode mask g 0 B) :
    Reach Q d f B (SInv base B mode mask g n) (20 * n) :=
  reach_loop (fun k => SInv base B mode mask g k) 20 n
    (fun k hk St h => scan_iter hP d f B mask g MB FB KB hB100 hB103 hB104 hB105 hB115 hB116
      hkey hflag hmask k hk St h) n le_rfl B h0

/-- Update loop invariant at pc `45`, relative to the state `E` at the start of the loop. -/
def UInv (base : ℕ) (E : State) (KB : ℤ) (d : Fin n → Fin n → ℝ) (b : Fin n) (x : ℕ)
    (St : State) : Prop :=
  St.cfg.pc = base + 45 ∧ St.output = none ∧ St.coins = E.coins ∧ St.queries = E.queries + x ∧
  St.imem = E.imem ∧ (∀ j, j ≠ 110 → j ≠ 111 → St.cfg.ptrs j = E.cfg.ptrs j) ∧
  St.cfg.ptrs 110 = x ∧ x ≤ n ∧
  (∀ j, (j < 100 ∨ 103 < j) → St.cfg.regs j = E.cfg.regs j) ∧
  (∀ v : Fin n, (v : ℕ) < x → St.cfg.mem (KB + (v : ℕ)) = min (E.cfg.mem (KB + (v : ℕ))) (d v b)) ∧
  (∀ z, ¬ (KB ≤ z ∧ z < KB + x) → St.cfg.mem z = E.cfg.mem z)

include hP in
lemma upd_iter (E : State) (KB : ℤ) (b : Fin n) (hE100 : E.cfg.ptrs 100 = n)
    (hE105 : E.cfg.ptrs 105 = KB) (hE113 : E.cfg.ptrs 113 = (b : ℕ))
    (x : ℕ) (hx : x < n) (St : State) (h : UInv base E KB d b x St) :
    Reach Q d f St (UInv base E KB d b (x + 1)) 10 := by
  obtain ⟨hpc, ho, hc, hq, himem, hp, h110, -, hr, hm1, hm2⟩ := h
  have e100 : St.cfg.ptrs 100 = n := by rw [hp 100 (by omega) (by omega), hE100]
  have e105 : St.cfg.ptrs 105 = KB := by rw [hp 105 (by omega) (by omega), hE105]
  have e113 : St.cfg.ptrs 113 = (b : ℕ) := by rw [hp 113 (by omega) (by omega), hE113]
  set x' : Fin n := ⟨x, hx⟩ with hx'
  have horc : oracleAnswer d (x : ℤ) ((b : ℕ) : ℤ) = d x' b := oracle_fin d x' b
  have hmx : St.cfg.mem (KB + (x : ℤ)) = E.cfg.mem (KB + (x : ℤ)) := hm2 _ (by omega)
  have hnx : ¬ (n : ℤ) ≤ x := by omega
  by_cases hle : E.cfg.mem (KB + (x : ℤ)) - d x' b ≤ 0
  · refine Reach.of_iter (s := 8) ?_ (by norm_num)
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp [UInv, step, ho, hpc, q45 hP, q46 hP, q47 hP, q48 hP, q49 hP, q50 hP, q52 hP, q53 hP,
      RAMStep, List.getElem?_map, State.next, Instr.coreOf, e100, e105, e113, h110, hnx, horc,
      hmx, hle, hc, hq, himem]
    refine ⟨by ring, fun j h1 h2 => ?_, hx, fun j hj => ?_, fun v hv => ?_,
      fun z hz => hm2 z (by omega)⟩
    · simp only [Function.update_apply]; split_ifs <;> first | omega | exact hp j h1 h2
    · simp only [Function.update_apply]; split_ifs <;> first | omega | exact hr j hj
    · rcases Nat.lt_or_eq_of_le hv with hv | hv
      · exact hm1 v hv
      · obtain rfl : v = x' := Fin.ext hv
        show St.cfg.mem (KB + (x : ℤ)) = min (E.cfg.mem (KB + (x : ℤ))) (d x' b)
        rw [hmx, min_eq_left (by linarith)]
  · refine Reach.of_iter (s := 9) ?_ (by norm_num)
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp [UInv, step, ho, hpc, q45 hP, q46 hP, q47 hP, q48 hP, q49 hP, q50 hP, q51 hP, q52 hP,
      q53 hP, RAMStep, List.getElem?_map, State.next, Instr.coreOf, e100, e105, e113, h110, hnx,
      horc, hmx, hle, hc, hq, himem]
    refine ⟨by ring, fun j h1 h2 => ?_, hx, fun j hj => ?_, fun v hv => ?_,
      fun z hz => ?_⟩
    · simp only [Function.update_apply]; split_ifs <;> first | omega | exact hp j h1 h2
    · simp only [Function.update_apply]; split_ifs <;> first | omega | exact hr j hj
    · rcases Nat.lt_or_eq_of_le hv with hv | hv
      · rw [Function.update_of_ne (by omega)]; exact hm1 v hv
      · obtain rfl : v = x' := Fin.ext hv
        show Function.update St.cfg.mem (KB + (x : ℤ)) (d x' b) (KB + (x : ℤ)) =
          min (E.cfg.mem (KB + (x : ℤ))) (d x' b)
        rw [Function.update_self, min_eq_right (by linarith)]
    · rw [Function.update_of_ne (by omega)]; exact hm2 z (by omega)

include hP in
lemma upd_run (E : State) (KB : ℤ) (b : Fin n) (hE100 : E.cfg.ptrs 100 = n)
    (hE105 : E.cfg.ptrs 105 = KB) (hE113 : E.cfg.ptrs 113 = (b : ℕ))
    (h0 : UInv base E KB d b 0 E) : Reach Q d f E (UInv base E KB d b n) (10 * n) :=
  reach_loop (fun k => UInv base E KB d b k) 10 n
    (fun k hk St h => upd_iter hP d f E KB b hE100 hE105 hE113 k hk St h) n le_rfl E h0

end
end MTSPGrow

end

section

set_option linter.unusedSimpArgs false
open scoped Classical

namespace MTSPGrow
open SublinearSteiner SmaleNinth MTSPMst

section
variable {mode : Bool} {base : ℕ} {Q : Program} (hP : Placed mode base Q) {n : ℕ}
  (d : Fin n → Fin n → ℝ) (f : ℕ → Bool)

include hP in
lemma outer_exit (St : State) (K j : ℕ) (hpc : St.cfg.pc = base + 14) (ho : St.output = none)
    (h102 : St.cfg.ptrs 102 = K) (h108 : St.cfg.ptrs 108 = j) (hKj : K ≤ j) :
    let S' := (step Q d f)^[1] St
    S'.cfg.pc = base + 55 ∧ S'.output = none ∧ S'.coins = St.coins ∧ S'.queries = St.queries ∧
    S'.cfg.regs = St.cfg.regs ∧ S'.cfg.ptrs = St.cfg.ptrs ∧ S'.cfg.mem = St.cfg.mem ∧
    S'.imem = St.imem := by
  have hc : (K : ℤ) ≤ j := by exact_mod_cast hKj
  simp [step, ho, hpc, q14 hP, RAMStep, List.getElem?_map, Instr.coreOf, h102, h108, hc]

include hP in
lemma outer_head (St : State) (K j : ℕ) (hpc : St.cfg.pc = base + 14) (ho : St.output = none)
    (h102 : St.cfg.ptrs 102 = K) (h108 : St.cfg.ptrs 108 = j) (hKj : ¬ K ≤ j) :
    let S' := (step Q d f)^[3] St
    S'.cfg.pc = base + 17 ∧ S'.output = none ∧ S'.coins = St.coins ∧ S'.queries = St.queries ∧
    S'.cfg.regs = St.cfg.regs ∧ S'.cfg.ptrs 110 = 0 ∧ S'.cfg.ptrs 114 = 0 ∧
    (∀ i, i ≠ 110 → i ≠ 114 → S'.cfg.ptrs i = St.cfg.ptrs i) ∧ S'.cfg.mem = St.cfg.mem ∧
    S'.imem = St.imem := by
  have hc : ¬ (K : ℤ) ≤ j := by exact_mod_cast hKj
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp [step, ho, hpc, q14 hP, q15 hP, q16 hP, RAMStep, List.getElem?_map, Instr.coreOf,
    State.next, h102, h108, hc]
  intro i h1 h2
  simp [h1, h2]

include hP in
lemma scan_end_none (C : State) (hpc : C.cfg.pc = base + 17) (ho : C.output = none)
    (h100 : C.cfg.ptrs 100 = n) (h110 : C.cfg.ptrs 110 = n) (h114 : C.cfg.ptrs 114 = 0)
    (h115 : C.cfg.ptrs 115 = 0) :
    let S' := (step Q d f)^[2] C
    S'.cfg.pc = base + 55 ∧ S'.output = none ∧ S'.coins = C.coins ∧ S'.queries = C.queries ∧
    S'.cfg.regs = C.cfg.regs ∧ S'.cfg.ptrs = C.cfg.ptrs ∧ S'.cfg.mem = C.cfg.mem ∧
    S'.imem = C.imem := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp [step, ho, hpc, q17 hP, q36 hP, RAMStep, List.getElem?_map, Instr.coreOf,
    State.next, h100, h110, h114, h115]

include hP in
lemma scan_end_found (C : State) (j : ℕ) (OV OW FB : ℤ) (b : ℤ) (hpc : C.cfg.pc = base + 17)
    (ho : C.output = none)
    (h100 : C.cfg.ptrs 100 = n) (h110 : C.cfg.ptrs 110 = n) (h114 : C.cfg.ptrs 114 = 1)
    (h115 : C.cfg.ptrs 115 = 0) (h116 : C.cfg.ptrs 116 = 1) (h108 : C.cfg.ptrs 108 = j)
    (h104 : C.cfg.ptrs 104 = FB) (h106 : C.cfg.ptrs 106 = OV) (h107 : C.cfg.ptrs 107 = OW)
    (h113 : C.cfg.ptrs 113 = b) :
    let S' := (step Q d f)^[10] C
    S'.cfg.pc = base + 45 ∧ S'.output = none ∧ S'.coins = C.coins ∧ S'.queries = C.queries ∧
    S'.cfg.regs = C.cfg.regs ∧ S'.cfg.ptrs 110 = 0 ∧ S'.cfg.ptrs 108 = j + 1 ∧
    (∀ i, i ≠ 108 → i ≠ 110 → i ≠ 111 → S'.cfg.ptrs i = C.cfg.ptrs i) ∧
    S'.cfg.mem = Function.update C.cfg.mem (OW + j) (C.cfg.regs 101) ∧
    S'.imem = Function.update (Function.update C.imem (OV + j) b) (FB + b) 1 := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp [step, ho, hpc, q17 hP, q36 hP, q37 hP, q38 hP, q39 hP, q40 hP, q41 hP, q42 hP, q43 hP,
    q44 hP, RAMStep, List.getElem?_map, Instr.coreOf,
    State.next, h100, h110, h114, h115, h116, h108, h104, h106, h107, h113]
  intro i h1 h2 h3
  simp [h1, h2, h3]

include hP in
lemma upd_end (F : State) (hpc : F.cfg.pc = base + 45) (ho : F.output = none)
    (h100 : F.cfg.ptrs 100 = n) (h110 : F.cfg.ptrs 110 = n) :
    let S' := (step Q d f)^[2] F
    S'.cfg.pc = base + 14 ∧ S'.output = none ∧ S'.coins = F.coins ∧ S'.queries = F.queries ∧
    S'.cfg.regs = F.cfg.regs ∧ S'.cfg.ptrs = F.cfg.ptrs ∧ S'.cfg.mem = F.cfg.mem ∧
    S'.imem = F.imem := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp [step, ho, hpc, q45 hP, q54 hP, RAMStep, List.getElem?_map, Instr.coreOf,
    State.next, h100, h110]

/-- The final state of the routine represents `R`. -/
def GDone (base : ℕ) (A : State) (n K : ℕ) (FB KB OV OW : ℤ) (R : GState n × List (Fin n × ℝ))
    (St : State) : Prop :=
  St.cfg.pc = base + 55 ∧ St.output = none ∧ St.coins = A.coins ∧
  St.queries = A.queries + n * (1 + R.2.length) ∧ St.cfg.ptrs 108 = R.2.length ∧
  (∀ j (hj : j < R.2.length), St.imem (OV + j) = ((R.2[j]).1 : ℕ) ∧
    St.cfg.mem (OW + j) = (R.2[j]).2) ∧
  (∀ u : Fin n, St.cfg.mem (KB + (u : ℕ)) = R.1.key u) ∧
  (∀ z, ¬ (FB ≤ z ∧ z < FB + n) → ¬ (OV ≤ z ∧ z < OV + K) → St.imem z = A.imem z) ∧
  (∀ z, ¬ (KB ≤ z ∧ z < KB + n) → ¬ (OW ≤ z ∧ z < OW + K) → St.cfg.mem z = A.cfg.mem z) ∧
  (∀ j, (j < 108 ∨ 140 ≤ j) → St.cfg.ptrs j = A.cfg.ptrs j) ∧
  (∀ j, (j < 100 ∨ 140 ≤ j) → St.cfg.regs j = A.cfg.regs j)

include hP in
lemma outer_exit_done (A : State) (K : ℕ) (FB KB OV OW : ℤ) (hA102 : A.cfg.ptrs 102 = K)
    (g : GState n) (L : List (Fin n × ℝ)) (j : ℕ) (St : State)
    (h : ORep base A n K FB KB OV OW (g, L) j St) (hKj : K ≤ j) :
    Reach Q d f St (GDone base A n K FB KB OV OW (g, L)) 1 := by
  obtain ⟨hpc, ho, hc, hq, h108, h115, h116, hp, hr, hlen, hjK, hkey, hflag, hout, hif, hmf⟩ := h
  simp only at hlen hkey hflag hout
  have e102 : St.cfg.ptrs 102 = K := by rw [hp 102 (by omega), hA102]
  have HS := outer_exit hP d f St K j hpc ho e102 h108 hKj
  dsimp only at HS
  obtain ⟨hSpc, hSo, hSc, hSq, hSr, hSp, hSmem, hSimem⟩ := HS
  refine Reach.of_iter (s := 1) ?_ le_rfl
  unfold GDone
  simp only
  refine ⟨hSpc, hSo, by rw [hSc, hc], by rw [hSq, hq, hlen], by rw [hSp, h108, hlen],
    fun i hi => by rw [hSimem, hSmem]; exact hout i hi, fun u => by rw [hSmem]; exact hkey u,
    fun z h1 h2 => by rw [hSimem]; exact hif z h1 h2, fun z h1 h2 => by rw [hSmem]; exact hmf z h1 h2,
    fun i hi => by rw [hSp]; exact hp i hi, fun i hi => by rw [hSr]; exact hr i hi⟩

include hP in
lemma outer_core (A : State) (mask : Fin n → Bool) (K : ℕ) (MB FB KB OV OW : ℤ)
    (hA100 : A.cfg.ptrs 100 = n) (hA102 : A.cfg.ptrs 102 = K) (hA103 : A.cfg.ptrs 103 = MB)
    (hA104 : A.cfg.ptrs 104 = FB) (hA105 : A.cfg.ptrs 105 = KB) (hA106 : A.cfg.ptrs 106 = OV)
    (hA107 : A.cfg.ptrs 107 = OW)
    (hMF : MB + n ≤ FB ∨ FB + n ≤ MB) (hMO : MB + n ≤ OV ∨ OV + K ≤ MB)
    (hFO : FB + n ≤ OV ∨ OV + K ≤ FB) (hKO : KB + n ≤ OW ∨ OW + K ≤ KB)
    (hmask : ∀ v : Fin n, mask v = decide (A.imem (MB + (v : ℕ)) ≠ 0))
    (g : GState n) (L : List (Fin n × ℝ)) (j : ℕ) (St : State)
    (h : ORep base A n K FB KB OV OW (g, L) j St) (hKj : ¬ K ≤ j) :
    Reach Q d f St (fun S' => (cands mask g = ∅ ∧ GDone base A n K FB KB OV OW (g, L) S') ∨
      (∃ b, IsBest mode g.key (cands mask g) b ∧
        ORep base A n K FB KB OV OW (⟨insert b g.S, fun x => min (g.key x) (d x b)⟩,
          L ++ [(b, g.key b)]) (j + 1) S'))
      (3 + (20 * n + (10 + (10 * n + 2)))) := by
  obtain ⟨hpc, ho, hc, hq, h108, h115, h116, hp, hr, hlen, hjK, hkey, hflag, hout, hif, hmf⟩ := h
  simp only at hlen hkey hflag hout
  have e100 : St.cfg.ptrs 100 = n := by rw [hp 100 (by omega), hA100]
  have e102 : St.cfg.ptrs 102 = K := by rw [hp 102 (by omega), hA102]
  have e103 : St.cfg.ptrs 103 = MB := by rw [hp 103 (by omega), hA103]
  have e104 : St.cfg.ptrs 104 = FB := by rw [hp 104 (by omega), hA104]
  have e105 : St.cfg.ptrs 105 = KB := by rw [hp 105 (by omega), hA105]
  have e106 : St.cfg.ptrs 106 = OV := by rw [hp 106 (by omega), hA106]
  have e107 : St.cfg.ptrs 107 = OW := by rw [hp 107 (by omega), hA107]
  have HB := outer_head hP d f St K j hpc ho e102 h108 hKj
  dsimp only at HB
  refine Reach.trans (P := fun B => B = (step Q d f)^[3] St) (Reach.of_iter rfl le_rfl)
    (fun B hB => ?_)
  rw [← hB] at HB
  obtain ⟨hBpc, hBo, hBc, hBq, hBr, hB110, hB114, hBp, hBmem, hBimem⟩ := HB
  have hB100 : B.cfg.ptrs 100 = n := by rw [hBp 100 (by omega) (by omega), e100]
  have hB103 : B.cfg.ptrs 103 = MB := by rw [hBp 103 (by omega) (by omega), e103]
  have hB104 : B.cfg.ptrs 104 = FB := by rw [hBp 104 (by omega) (by omega), e104]
  have hB105 : B.cfg.ptrs 105 = KB := by rw [hBp 105 (by omega) (by omega), e105]
  have hB106 : B.cfg.ptrs 106 = OV := by rw [hBp 106 (by omega) (by omega), e106]
  have hB107 : B.cfg.ptrs 107 = OW := by rw [hBp 107 (by omega) (by omega), e107]
  have hB108 : B.cfg.ptrs 108 = j := by rw [hBp 108 (by omega) (by omega), h108]
  have hB115 : B.cfg.ptrs 115 = 0 := by rw [hBp 115 (by omega) (by omega), h115]
  have hB116 : B.cfg.ptrs 116 = 1 := by rw [hBp 116 (by omega) (by omega), h116]
  have hkeyB : ∀ v : Fin n, B.cfg.mem (KB + (v : ℕ)) = g.key v := fun v => by
    rw [hBmem]; exact hkey v
  have hflagB : ∀ v : Fin n, B.imem (FB + (v : ℕ)) = if v ∈ g.S then 1 else 0 := fun v => by
    rw [hBimem]; exact hflag v
  have hmaskB : ∀ v : Fin n, mask v = decide (B.imem (MB + (v : ℕ)) ≠ 0) := fun v => by
    have := v.isLt
    rw [hBimem, hif _ (by omega) (by omega), hmask v]
  have hS0 : SInv base B mode mask g 0 B :=
    ⟨hBpc, hBo, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, by simpa using hB110,
      Nat.zero_le _, Or.inl ⟨candsLt_zero _ _, hB114⟩⟩
  refine Reach.trans (scan_run hP d f B mask g MB FB KB hB100 hB103 hB104 hB105 hB115 hB116
    hkeyB hflagB hmaskB hS0) (fun C hC => ?_)
  obtain ⟨hCpc, hCo, hCc, hCq, hCmem, hCimem, hCp, hCr, hC110, -, hCbest⟩ := hC
  have hC100 : C.cfg.ptrs 100 = n := by rw [hCp 100 (by omega), hB100]
  have hC104 : C.cfg.ptrs 104 = FB := by rw [hCp 104 (by omega), hB104]
  have hC105 : C.cfg.ptrs 105 = KB := by rw [hCp 105 (by omega), hB105]
  have hC106 : C.cfg.ptrs 106 = OV := by rw [hCp 106 (by omega), hB106]
  have hC107 : C.cfg.ptrs 107 = OW := by rw [hCp 107 (by omega), hB107]
  have hC108 : C.cfg.ptrs 108 = j := by rw [hCp 108 (by omega), hB108]
  have hC115 : C.cfg.ptrs 115 = 0 := by rw [hCp 115 (by omega), hB115]
  have hC116 : C.cfg.ptrs 116 = 1 := by rw [hCp 116 (by omega), hB116]
  rw [candsLt_n] at hCbest
  rcases hCbest with ⟨h0, hC114⟩ | ⟨b, hb, hC114, hC113, hC101⟩
  · have HS := scan_end_none hP d f C hCpc hCo hC100 hC110 hC114 hC115
    dsimp only at HS
    obtain ⟨hSpc, hSo, hSc, hSq, hSr, hSp, hSmem, hSimem⟩ := HS
    refine Reach.of_iter (s := 2) ?_ (by omega)
    refine Or.inl ⟨h0, ?_⟩
    have hm' : ((step Q d f)^[2] C).cfg.mem = St.cfg.mem := by rw [hSmem, hCmem, hBmem]
    have hi' : ((step Q d f)^[2] C).imem = St.imem := by rw [hSimem, hCimem, hBimem]
    unfold GDone
    simp only
    refine ⟨hSpc, hSo, by rw [hSc, hCc, hBc, hc], by rw [hSq, hCq, hBq, hq, hlen],
      by rw [hSp, hC108, hlen], fun i hi => by rw [hi', hm']; exact hout i hi,
      fun u => by rw [hm']; exact hkey u, fun z h1 h2 => by rw [hi']; exact hif z h1 h2,
      fun z h1 h2 => by rw [hm']; exact hmf z h1 h2, fun i hi => ?_, fun i hi => ?_⟩
    · rw [hSp, hCp i (by omega), hBp i (by omega) (by omega)]; exact hp i hi
    · rw [hSr, hCr i (by omega), hBr]; exact hr i hi
  · have hbn := b.isLt
    have HE := scan_end_found hP d f C j OV OW FB ((b : ℕ) : ℤ) hCpc hCo hC100 hC110 hC114 hC115
      hC116 hC108 hC104 hC106 hC107 hC113
    dsimp only at HE
    refine Reach.trans (P := fun E => E = (step Q d f)^[10] C) (Reach.of_iter rfl le_rfl)
      (fun E hE => ?_)
    rw [← hE] at HE
    obtain ⟨hEpc, hEo, hEc, hEq, hEr, hE110, hE108, hEp, hEmem, hEimem⟩ := HE
    have hE100 : E.cfg.ptrs 100 = n := by rw [hEp 100 (by omega) (by omega) (by omega), hC100]
    have hE105 : E.cfg.ptrs 105 = KB := by rw [hEp 105 (by omega) (by omega) (by omega), hC105]
    have hE113 : E.cfg.ptrs 113 = (b : ℕ) := by
      rw [hEp 113 (by omega) (by omega) (by omega), hC113]
    have hU0 : UInv base E KB d b 0 E :=
      ⟨hEpc, hEo, rfl, by simp, rfl, fun _ _ _ => rfl, by simpa using hE110, Nat.zero_le _,
        fun _ _ => rfl, fun v hv => absurd hv (Nat.not_lt_zero _), fun _ _ => rfl⟩
    refine Reach.trans (upd_run hP d f E KB b hE100 hE105 hE113 hU0) (fun F hF => ?_)
    obtain ⟨hFpc, hFo, hFc, hFq, hFimem, hFp, hF110, -, hFr, hFm1, hFm2⟩ := hF
    have hF100 : F.cfg.ptrs 100 = n := by rw [hFp 100 (by omega) (by omega), hE100]
    have HS := upd_end hP d f F hFpc hFo hF100 hF110
    dsimp only at HS
    obtain ⟨hSpc, hSo, hSc, hSq, hSr, hSp, hSmem, hSimem⟩ := HS
    refine Reach.of_iter (s := 2) ?_ le_rfl
    refine Or.inr ⟨b, hb, ?_⟩
    unfold ORep
    simp only
    refine ⟨hSpc, hSo, by rw [hSc, hFc, hEc, hCc, hBc, hc], ?_, ?_, ?_, ?_, fun i hi => ?_,
      fun i hi => ?_, by simp [hlen], by omega, fun v => ?_, fun v => ?_, fun i hi => ?_,
      fun z h1 h2 => ?_, fun z h1 h2 => ?_⟩
    · rw [hSq, hFq, hEq, hCq, hBq, hq]; ring
    · rw [hSp, hFp 108 (by omega) (by omega), hE108]; push_cast; ring
    · rw [hSp, hFp 115 (by omega) (by omega), hEp 115 (by omega) (by omega) (by omega), hC115]
    · rw [hSp, hFp 116 (by omega) (by omega), hEp 116 (by omega) (by omega) (by omega), hC116]
    · rw [hSp, hFp i (by omega) (by omega), hEp i (by omega) (by omega) (by omega),
        hCp i (by omega), hBp i (by omega) (by omega)]
      exact hp i hi
    · rw [hSr, hFr i (by omega), hEr, hCr i (by omega), hBr]; exact hr i hi
    · have := v.isLt
      rw [hSmem, hFm1 v v.isLt, hEmem, Function.update_of_ne (by omega), hCmem, hBmem, hkey v]
    · have := v.isLt
      rw [hSimem, hFimem, hEimem]
      by_cases hv : v = b
      · subst hv; simp
      · have hv' : (v : ℕ) ≠ (b : ℕ) := fun h => hv (Fin.ext h)
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hCimem, hBimem,
          hflag v]
        simp [Finset.mem_insert, hv]
    · simp only [List.length_append, List.length_singleton] at hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi' | hi'
      · rw [List.getElem_append_left hi']
        obtain ⟨o1, o2⟩ := hout i hi'
        constructor
        · rw [hSimem, hFimem, hEimem, Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), hCimem, hBimem, o1]
        · rw [hSmem, hFm2 _ (by omega), hEmem, Function.update_of_ne (by omega), hCmem, hBmem, o2]
      · subst hi'
        rw [List.getElem_append_right (le_refl _)]
        simp only [Nat.sub_self, List.getElem_cons_zero]
        constructor
        · rw [hSimem, hFimem, hEimem, Function.update_of_ne (by omega), hlen,
            Function.update_self]
        · rw [hSmem, hFm2 _ (by omega), hEmem, hlen, Function.update_self, hC101]
    · rw [hSimem, hFimem, hEimem, Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), hCimem, hBimem, hif z h1 h2]
    · rw [hSmem, hFm2 z (by omega), hEmem, Function.update_of_ne (by omega), hCmem, hBmem,
        hmf z h1 h2]

end
end MTSPGrow

end

section

/-!
# Greedy growth (Prim / farthest-first traversal) on the distance-oracle RAM

`growCode mode base` (in `Solutions.W.GrowCode`) and its correctness theorem `grow_run`:
the routine computes `MTSPMst.grun d mode (maskOf St MB) start K` — final keys in `[KB, KB+n)`,
recorded vertices in `[OV, OV+K)`, recorded values in `[OW, OW+K)`, count in pointer `108` —
in at most `40 (K+1)(n+1)` steps with exactly `n (1 + #recorded)` oracle queries.
-/

open scoped Classical

namespace MTSPGrow
open SublinearSteiner SmaleNinth MTSPMst

section
variable {mode : Bool} {base : ℕ} {Q : Program} (hP : Placed mode base Q) {n : ℕ}
  (d : Fin n → Fin n → ℝ) (f : ℕ → Bool)

include hP in
lemma outer_loop (A : State) (start : Fin n) (K : ℕ) (MB FB KB OV OW : ℤ)
    (hA100 : A.cfg.ptrs 100 = n) (hA102 : A.cfg.ptrs 102 = K) (hA103 : A.cfg.ptrs 103 = MB)
    (hA104 : A.cfg.ptrs 104 = FB) (hA105 : A.cfg.ptrs 105 = KB) (hA106 : A.cfg.ptrs 106 = OV)
    (hA107 : A.cfg.ptrs 107 = OW)
    (hMF : MB + n ≤ FB ∨ FB + n ≤ MB) (hMO : MB + n ≤ OV ∨ OV + K ≤ MB)
    (hFO : FB + n ≤ OV ∨ OV + K ≤ FB) (hKO : KB + n ≤ OW ∨ OW + K ≤ KB) :
    ∀ m j St, K - j = m →
      ORep base A n K FB KB OV OW (grun d mode (maskOf A MB) start j) j St →
      Reach Q d f St (GDone base A n K FB KB OV OW (grun d mode (maskOf A MB) start K))
        (30 * (n + 1) * (m + 1)) := by
  intro m
  induction m with
  | zero =>
    intro j St hm h
    have hKj : K ≤ j := by omega
    have hjK := h.2.2.2.2.2.2.2.2.2.2.1
    obtain rfl : j = K := by omega
    exact (outer_exit_done hP d f A j FB KB OV OW hA102 _ _ j St h hKj).mono (by nlinarith)
  | succ m ih =>
    intro j St hm h
    have hKj : ¬ K ≤ j := by omega
    have core := outer_core hP d f A (maskOf A MB) K MB FB KB OV OW hA100 hA102 hA103 hA104
      hA105 hA106 hA107 hMF hMO hFO hKO (fun v => rfl) _ _ j St h hKj
    have hb : 3 + (20 * n + (10 + (10 * n + 2))) + 30 * (n + 1) * (m + 1) ≤
        30 * (n + 1) * (m + 1 + 1) := by nlinarith
    refine (Reach.trans core (fun S' hS' => ?_)).mono hb
    rcases hS' with ⟨hempty, hdone⟩ | ⟨b, hb, hrep⟩
    · have hne : ¬ (cands (maskOf A MB) (grun d mode (maskOf A MB) start j).1).Nonempty := by
        rw [hempty]; simp
      have hst := grun_stable d mode (maskOf A MB) start j hne (K - j)
      rw [show j + (K - j) = K by omega] at hst
      refine Reach.of_iter (s := 0) ?_ (Nat.zero_le _)
      rw [hst]
      exact hdone
    · have hne : (cands (maskOf A MB) (grun d mode (maskOf A MB) start j).1).Nonempty :=
        ⟨b, hb.1⟩
      have hgs := grun_succ_some d mode (maskOf A MB) start j hne
      rw [pick_eq mode (maskOf A MB) _ hne b hb] at hgs
      rw [← hgs] at hrep
      exact ih (j + 1) S' (by omega) hrep

end

/-- **Greedy growth** (strong form, with the exact query count). Running `growCode mode base` (placed at `base` in `Q`) from `St` performs
`K` steps of greedy growth (`MTSPMst.grun`) on the masked points, within `40 (K+1)(n+1)` steps
and with exactly `n (1 + #recorded)` distance queries. -/
theorem grow_run_exact (mode : Bool) (Q : Program) (base : ℕ)
    (hQ : ∀ i < (growCode mode base).length, Q[base + i]? = (growCode mode base)[i]?)
    {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (f : ℕ → Bool) (St : State)
    (start : Fin n) (K : ℕ) (MB FB KB OV OW : ℤ)
    (hpc : St.cfg.pc = base) (hout : St.output = none)
    (h100 : St.cfg.ptrs 100 = n) (h101 : St.cfg.ptrs 101 = start) (h102 : St.cfg.ptrs 102 = K)
    (h103 : St.cfg.ptrs 103 = MB) (h104 : St.cfg.ptrs 104 = FB) (h105 : St.cfg.ptrs 105 = KB)
    (h106 : St.cfg.ptrs 106 = OV) (h107 : St.cfg.ptrs 107 = OW)
    (hMF : MB + n ≤ FB ∨ FB + n ≤ MB) (hMO : MB + n ≤ OV ∨ OV + K ≤ MB)
    (hFO : FB + n ≤ OV ∨ OV + K ≤ FB) (hKO : KB + n ≤ OW ∨ OW + K ≤ KB) :
    ∃ T ≤ 40 * (K + 1) * (n + 1),
      ((step Q d f)^[T] St).cfg.pc = base + (growCode mode base).length ∧
      ((step Q d f)^[T] St).output = none ∧
      ((step Q d f)^[T] St).coins = St.coins ∧
      ((step Q d f)^[T] St).queries =
        St.queries + n * (1 + (grun d mode (maskOf St MB) start K).2.length) ∧
      ((step Q d f)^[T] St).queries ≤ St.queries + (K + 1) * n ∧
      ((step Q d f)^[T] St).cfg.ptrs 108 = (grun d mode (maskOf St MB) start K).2.length ∧
      (∀ j (hj : j < (grun d mode (maskOf St MB) start K).2.length),
        ((step Q d f)^[T] St).imem (OV + j) = (((grun d mode (maskOf St MB) start K).2[j]).1 : ℕ) ∧
        ((step Q d f)^[T] St).cfg.mem (OW + j) = ((grun d mode (maskOf St MB) start K).2[j]).2) ∧
      (∀ u : Fin n, ((step Q d f)^[T] St).cfg.mem (KB + u) =
        (grun d mode (maskOf St MB) start K).1.key u) ∧
      (∀ z : ℤ, ¬ (FB ≤ z ∧ z < FB + n) → ¬ (OV ≤ z ∧ z < OV + K) →
        ((step Q d f)^[T] St).imem z = St.imem z) ∧
      (∀ z : ℤ, ¬ (KB ≤ z ∧ z < KB + n) → ¬ (OW ≤ z ∧ z < OW + K) →
        ((step Q d f)^[T] St).cfg.mem z = St.cfg.mem z) ∧
      (∀ j, (j < 100 ∨ 140 ≤ j) → ((step Q d f)^[T] St).cfg.ptrs j = St.cfg.ptrs j) ∧
      (∀ j, 100 ≤ j → j < 108 → ((step Q d f)^[T] St).cfg.ptrs j = St.cfg.ptrs j) ∧
      (∀ j, (j < 100 ∨ 140 ≤ j) → ((step Q d f)^[T] St).cfg.regs j = St.cfg.regs j) := by
  have hP : Placed mode base Q := fun i hi => hQ i (by rw [growCode_length]; exact hi)
  have hinit := init_run hP d f St K KB FB OV OW start hpc hout h100 h101 h104 h105
  have hall := Reach.trans hinit (fun B hB => outer_loop hP d f St start K MB FB KB OV OW h100
    h102 h103 h104 h105 h106 h107 hMF hMO hFO hKO K 0 B (by omega) hB)
  have hbound : 8 * n + 7 + 30 * (n + 1) * (K + 1) ≤ 40 * (K + 1) * (n + 1) := by nlinarith
  obtain ⟨T, hT, hG⟩ := hall.mono hbound
  refine ⟨T, hT, ?_⟩
  obtain ⟨hGpc, hGo, hGc, hGq, hG108, hGout, hGkey, hGi, hGm, hGp, hGr⟩ := hG
  have hlen := grun_length_le d mode (maskOf St MB) start K
  refine ⟨by rw [hGpc, growCode_length], hGo, hGc, hGq, ?_, hG108, hGout, hGkey, hGi, hGm,
    fun j hj => hGp j (by omega), fun j h1 h2 => hGp j (by omega), hGr⟩
  rw [hGq]
  have : n * (1 + (grun d mode (maskOf St MB) start K).2.length) ≤ (K + 1) * n := by
    rw [mul_comm]; exact Nat.mul_le_mul_right n (by omega)
  omega

/-- **Greedy growth** (interface form). -/
theorem grow_run (mode : Bool) (Q : Program) (base : ℕ)
    (hQ : ∀ i < (growCode mode base).length, Q[base + i]? = (growCode mode base)[i]?)
    {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (f : ℕ → Bool) (St : State)
    (start : Fin n) (K : ℕ) (MB FB KB OV OW : ℤ)
    (hpc : St.cfg.pc = base) (hout : St.output = none)
    (h100 : St.cfg.ptrs 100 = n) (h101 : St.cfg.ptrs 101 = start) (h102 : St.cfg.ptrs 102 = K)
    (h103 : St.cfg.ptrs 103 = MB) (h104 : St.cfg.ptrs 104 = FB) (h105 : St.cfg.ptrs 105 = KB)
    (h106 : St.cfg.ptrs 106 = OV) (h107 : St.cfg.ptrs 107 = OW)
    (hMF : MB + n ≤ FB ∨ FB + n ≤ MB) (hMO : MB + n ≤ OV ∨ OV + K ≤ MB)
    (hFO : FB + n ≤ OV ∨ OV + K ≤ FB) (hKO : KB + n ≤ OW ∨ OW + K ≤ KB) :
    ∃ T ≤ 40 * (K + 1) * (n + 1) + 0,
      ((step Q d f)^[T] St).cfg.pc = base + (growCode mode base).length ∧
      ((step Q d f)^[T] St).output = none ∧
      ((step Q d f)^[T] St).coins = St.coins ∧
      ((step Q d f)^[T] St).queries ≤ St.queries + (K + 1) * n ∧
      ((step Q d f)^[T] St).cfg.ptrs 108 = (grun d mode (maskOf St MB) start K).2.length ∧
      (∀ j (hj : j < (grun d mode (maskOf St MB) start K).2.length),
        ((step Q d f)^[T] St).imem (OV + j) = (((grun d mode (maskOf St MB) start K).2[j]).1 : ℕ) ∧
        ((step Q d f)^[T] St).cfg.mem (OW + j) = ((grun d mode (maskOf St MB) start K).2[j]).2) ∧
      (∀ u : Fin n, ((step Q d f)^[T] St).cfg.mem (KB + u) =
        (grun d mode (maskOf St MB) start K).1.key u) ∧
      (∀ z : ℤ, ¬ (FB ≤ z ∧ z < FB + n) → ¬ (OV ≤ z ∧ z < OV + K) →
        ((step Q d f)^[T] St).imem z = St.imem z) ∧
      (∀ z : ℤ, ¬ (KB ≤ z ∧ z < KB + n) → ¬ (OW ≤ z ∧ z < OW + K) →
        ((step Q d f)^[T] St).cfg.mem z = St.cfg.mem z) ∧
      (∀ j, (j < 100 ∨ 140 ≤ j) → ((step Q d f)^[T] St).cfg.ptrs j = St.cfg.ptrs j) ∧
      (∀ j, 100 ≤ j → j < 108 → ((step Q d f)^[T] St).cfg.ptrs j = St.cfg.ptrs j) ∧
      (∀ j, (j < 100 ∨ 140 ≤ j) → ((step Q d f)^[T] St).cfg.regs j = St.cfg.regs j) := by
  obtain ⟨T, hT, h1, h2, h3, -, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    grow_run_exact mode Q base hQ d hd f St start K MB FB KB OV OW hpc hout h100 h101 h102 h103
      h104 h105 h106 h107 hMF hMO hFO hKO
  exact ⟨T, by omega, h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

end MTSPGrow

end

section

/-! Code blocks of the MST-weight estimator.

Pointer registers: `0` zero, `1` n, `2` q, `3` k, `4` s, `5` r, `6` m, `7` N = 2^m, `8` L = n + s,
`9` FB = KB = -L, `10` OV = OW = -2L, `11` MB2 = -3L, `12` one, `13` k-1, `14` outer counter,
`15` k', `16..18` recorded counts, `20` loop counter j, `21` address, `22` countUp counter,
`23` mask base / `24` K / `25` start arguments, `26` coin counter, `27, 28` scratch.
Real registers: `0` zero, `1` T1, `2` A', `3` H, `4` T0, others scratch. -/

open scoped Classical

namespace MTSPEst
open SublinearSteiner SmaleNinth

/-- `n := I[0]`; halt with `0` if `n ≤ 1`. Exit at `b + 6`. -/
def setupCode (b : ℕ) : Program :=
  [ .integerLoad 1 0,
    .core (.pset 12 1),
    .core (.pjle 1 12 (b + 4)),
    .core (.pjle 0 0 (b + 6)),
    .core (.const 5 ((0 : ℚ) : ℝ)),
    .halt 5 ]

/-- `q :=` least `q ≥ 1` with `n ≤ q^4`. Exit at `b + 9`. -/
def qloopCode (b : ℕ) : Program :=
  [ .core (.pset 2 1),
    .pointerReal 5 2,
    .core (.mul 6 5 5),
    .core (.mul 6 6 6),
    .pointerReal 7 1,
    .core (.sub 8 7 6),
    .core (.jle 8 (b + 9)),
    .core (.pinc 2),
    .core (.pjle 0 0 (b + 1)) ]

/-- `p22 :=` the natural number in `r25`. Exit at `b + 6`. -/
def countUpCode (b : ℕ) : Program :=
  [ .core (.pset 22 0),
    .pointerReal 13 22,
    .core (.sub 14 25 13),
    .core (.jle 14 (b + 6)),
    .core (.pinc 22),
    .core (.pjle 0 0 (b + 1)) ]

/-- `r25 := K1 q^3`. -/
def paramA (K1 : ℕ) : Program :=
  [ .pointerReal 9 2,
    .core (.mul 10 9 9),
    .core (.mul 11 10 9),
    .core (.const 12 ((K1 : ℚ) : ℝ)),
    .core (.mul 25 12 11) ]

/-- `k := min n p22`, `r25 := S1 q`. -/
def paramB (S1 : ℕ) (b : ℕ) : Program :=
  [ .core (.pcopy 15 22),
    .core (.pcopy 3 1),
    .core (.pjle 1 15 (b + 4)),
    .core (.pcopy 3 15),
    .core (.const 12 ((S1 : ℚ) : ℝ)),
    .core (.mul 25 12 9) ]

/-- `s := p22`, `r25 := R1 q^2`. -/
def paramC (R1 : ℕ) : Program :=
  [ .core (.pcopy 4 22),
    .core (.const 12 ((R1 : ℚ) : ℝ)),
    .core (.mul 25 12 10) ]

/-- `r := p22`. -/
def paramD : Program := [ .core (.pcopy 5 22) ]

/-- `m :=` least `m` with `n ≤ 2^m`, `N := 2^m`. Exit at `b + 6`. -/
def mloopCode (b : ℕ) : Program :=
  [ .core (.pset 6 0),
    .core (.pset 7 1),
    .core (.pjle 1 7 (b + 6)),
    .pointerAdd 7 7 7,
    .core (.pinc 6),
    .core (.pjle 0 0 (b + 2)) ]

/-- Memory layout and arguments of the first call. -/
def layoutCode : Program :=
  [ .core (.pcopy 13 3),
    .core (.pdec 13),
    .pointerAdd 8 1 4,
    .pointerSub 9 0 8,
    .pointerAdd 10 9 9,
    .pointerAdd 11 10 9,
    .core (.pset 25 0),
    .core (.pcopy 24 13),
    .core (.pcopy 23 12) ]

/-- The prefix, at position `0`; length `63`. -/
def pre0 (K1 S1 R1 : ℕ) : Program :=
  setupCode 0 ++ (qloopCode 6 ++ (paramA K1 ++ (countUpCode 20 ++ (paramB S1 26 ++
    (countUpCode 32 ++ (paramC R1 ++ (countUpCode 41 ++ (paramD ++ (mloopCode 48 ++
    layoutCode)))))))))

/-- Arguments of the subroutine. -/
def callArgs : Program :=
  [ .core (.pcopy 100 1), .core (.pcopy 101 25), .core (.pcopy 102 24), .core (.pcopy 103 23),
    .core (.pcopy 104 9), .core (.pcopy 105 9), .core (.pcopy 106 10), .core (.pcopy 107 10) ]

/-- A call of the subroutine at position `b`. -/
noncomputable def callCode (mode : Bool) (b : ℕ) : Program :=
  callArgs ++ MTSPGrow.growCode mode (b + 8)

/-- `T0 := max (0, key[0..n))` into `r4`. Exit at `b + 11`. -/
def t0Code (b : ℕ) : Program :=
  [ .core (.const 4 ((0 : ℚ) : ℝ)),
    .core (.pset 20 0),
    .core (.pcopy 21 9),
    .core (.pjle 1 20 (b + 11)),
    .core (.load 5 21),
    .core (.sub 6 5 4),
    .core (.jle 6 (b + 8)),
    .core (.add 4 4 6),
    .core (.pinc 20),
    .core (.pinc 21),
    .core (.pjle 0 0 (b + 3)) ]

/-- `T1 := T0 * cinv`. -/
def t1Code (cinv : ℚ) : Program :=
  [ .core (.const 7 (cinv : ℝ)), .core (.mul 1 4 7) ]

/-- Net mask at `MB2`: mark `0` and the recorded vertices. Exit at `b + 10`. -/
def markCode (b : ℕ) : Program :=
  [ .integerStore 11 12,
    .core (.pset 20 0),
    .core (.pcopy 21 10),
    .core (.pjle 16 20 (b + 10)),
    .integerLoad 27 21,
    .pointerAdd 28 11 27,
    .integerStore 28 12,
    .core (.pinc 20),
    .core (.pinc 21),
    .core (.pjle 0 0 (b + 3)) ]

/-- Arguments of the second call. -/
def call2Args : Program := [ .core (.pset 25 0), .core (.pcopy 24 13), .core (.pcopy 23 11) ]

/-- Code between the first and the second call (length `27`). -/
def A1code (cinv : ℚ) (b : ℕ) : Program :=
  [.core (.pcopy 16 108)] ++ (t0Code (b + 1) ++ (t1Code cinv ++ (markCode (b + 14) ++ call2Args)))

/-- `A' := Σ max (U_j - T1) 0` into `r2`. Exit at `b + 11`. -/
def apCode (b : ℕ) : Program :=
  [ .core (.const 2 ((0 : ℚ) : ℝ)),
    .core (.pset 20 0),
    .core (.pcopy 21 10),
    .core (.pjle 17 20 (b + 11)),
    .core (.load 5 21),
    .core (.sub 6 5 1),
    .core (.jle 6 (b + 8)),
    .core (.add 2 2 6),
    .core (.pinc 20),
    .core (.pinc 21),
    .core (.pjle 0 0 (b + 3)) ]

/-- `H := 0`, `i := 0`. -/
def hinitCode : Program := [ .core (.const 3 ((0 : ℚ) : ℝ)), .core (.pset 14 0) ]

/-- Read `m` coins MSB-first into `p25`. Exit at `b + 9`. -/
def coinCode (b : ℕ) : Program :=
  [ .core (.pset 25 0),
    .core (.pset 26 0),
    .core (.pjle 6 26 (b + 9)),
    .coin 5,
    .pointerAdd 25 25 25,
    .core (.jle 5 (b + 7)),
    .core (.pinc 25),
    .core (.pinc 26),
    .core (.pjle 0 0 (b + 2)) ]

/-- If `n ≤ u` skip the call; else arguments of the third call. -/
def testCode (skip : ℕ) : Program :=
  [ .core (.pjle 1 25 skip), .core (.pcopy 24 4), .core (.pcopy 23 12) ]

/-- Code between the second and the third call (length `27`); the outer loop head is at
`b + 14`. -/
def A2code (b skip exit : ℕ) : Program :=
  [.core (.pcopy 17 108)] ++ (apCode (b + 1) ++ (hinitCode ++ ([.core (.pjle 5 14 exit)] ++
    (coinCode (b + 15) ++ testCode skip))))

/-- `r15 := cap(j, pm)`, `j = p20`, `pm = r11`. Exit at `b + 6`. -/
def capCode (b : ℕ) : Program :=
  [ .core (.pjle 1 20 (b + 3)),
    .core (.sub 14 11 1),
    .core (.jle 14 (b + 5)),
    .core (.add 15 1 0),
    .core (.pjle 0 0 (b + 6)),
    .core (.add 15 11 0) ]

def hA : Program :=
  [ .core (.const 10 ((0 : ℚ) : ℝ)), .core (.const 11 ((0 : ℚ) : ℝ)), .core (.pset 20 0),
    .core (.pcopy 21 10) ]

def hB (b : ℕ) : Program :=
  [ .core (.add 12 15 0),
    .core (.pjle 4 20 (b + 31)),
    .core (.pjle 18 20 (b + 17)),
    .core (.load 16 21),
    .core (.sub 17 16 11),
    .core (.jle 17 (b + 17)),
    .core (.add 11 11 17),
    .core (.pinc 20),
    .core (.pinc 21) ]

def hC (b : ℕ) : Program :=
  [ .core (.sub 18 15 12),
    .core (.add 12 12 18),
    .pointerReal 19 20,
    .core (.div 18 18 19),
    .core (.add 10 10 18),
    .core (.pjle 0 0 (b + 11)) ]

/-- `h` into `r10`. Exit at `b + 31`. -/
def hloopCode (b : ℕ) : Program :=
  hA ++ (capCode (b + 4) ++ (hB b ++ (capCode (b + 19) ++ hC b)))

/-- Output. -/
def finalCode (scale : ℚ) : Program :=
  [ .pointerReal 20 7,
    .pointerReal 21 5,
    .core (.div 22 20 21),
    .core (.mul 23 22 3),
    .core (.add 24 2 23),
    .core (.sub 25 24 1),
    .core (.const 26 (scale : ℝ)),
    .core (.mul 27 25 26),
    .halt 27 ]

/-- `H := H + h`, `i := i + 1`, back to the outer head. -/
def tailCode (oh : ℕ) : Program := [ .core (.add 3 3 10), .core (.pinc 14), .core (.pjle 0 0 oh) ]

/-- Code after the third call (length `44`); skip target `b + 33`, exit target `b + 35`. -/
def A3code (scale : ℚ) (b oh : ℕ) : Program :=
  [.core (.pcopy 18 108)] ++ (hloopCode (b + 1) ++ (tailCode oh ++ finalCode scale))

/-! Positions. -/

noncomputable def b1 : ℕ := 71 + (MTSPGrow.growCode true 71).length
noncomputable def g2 : ℕ := b1 + 27
noncomputable def b2 : ℕ := g2 + 8 + (MTSPGrow.growCode false (g2 + 8)).length
noncomputable def g3 : ℕ := b2 + 27
noncomputable def b3 : ℕ := g3 + 8 + (MTSPGrow.growCode false (g3 + 8)).length

/-- The estimator program. -/
noncomputable def estProg (K1 S1 R1 : ℕ) (cinv scale : ℚ) : Program :=
  pre0 K1 S1 R1 ++ (callCode true 63 ++ (A1code cinv b1 ++ (callCode false g2 ++
    (A2code b2 (b3 + 33) (b3 + 35) ++ (callCode false g3 ++ A3code scale b3 (b2 + 14))))))

end MTSPEst

end

section

/-!
Facts about threshold-graph components: net sandwich, separated representatives,
monotonicity of component sizes, and `compCount = Σ_v 1 / compSize v`.
-/

open scoped Classical

namespace MTSPMst
open Finset

variable {n : ℕ}

lemma card_image_le_of_factor {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (s : Finset α)
    (f : α → β) (g : α → γ) (h : ∀ a ∈ s, ∀ b ∈ s, f a = f b → g a = g b) :
    (s.image g).card ≤ (s.image f).card := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a0, _⟩
  · simp
  have : Nonempty α := ⟨a0⟩
  have key : ∀ c ∈ s.image g, ∃ a ∈ s, g a = c := fun c hc => by simpa using hc
  choose! sec hsec hsec' using key
  refine Finset.card_le_card_of_injOn (fun c => f (sec c)) ?_ ?_
  · intro c hc; exact Finset.mem_image_of_mem f (hsec c hc)
  · intro c hc c' hc' he
    have := h _ (hsec c hc) _ (hsec c' hc') he
    rw [hsec' c hc, hsec' c' hc'] at this
    exact this

lemma thrGraph_adj_iff (d : Fin n → Fin n → ℝ) (hsymm : ∀ x y, d x y = d y x)
    (Q : Finset (Fin n)) (t : ℝ) (u v : Fin n) :
    (thrGraph d Q t).Adj u v ↔ u ≠ v ∧ u ∈ Q ∧ v ∈ Q ∧ d u v ≤ t := by
  unfold thrGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, h.2.1, h.1, by rw [hsymm]; exact h.2.2⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

lemma thr_reach_of_close (d : Fin n → Fin n → ℝ) (hsymm : ∀ x y, d x y = d y x)
    (Q : Finset (Fin n)) (t : ℝ) {u v : Fin n} (hu : u ∈ Q) (hv : v ∈ Q) (huv : d u v ≤ t) :
    (thrGraph d Q t).Reachable u v := by
  by_cases h : u = v
  · subst h; rfl
  · exact SimpleGraph.Adj.reachable ((thrGraph_adj_iff d hsymm Q t u v).mpr ⟨h, hu, hv, huv⟩)

lemma thrGraph_mono (d : Fin n → Fin n → ℝ) (hsymm : ∀ x y, d x y = d y x)
    {Q Q' : Finset (Fin n)} (hQ : Q ⊆ Q') {t t' : ℝ} (ht : t ≤ t') :
    thrGraph d Q t ≤ thrGraph d Q' t' := by
  intro u v h
  rw [thrGraph_adj_iff d hsymm] at h ⊢
  exact ⟨h.1, hQ h.2.1, hQ h.2.2.1, h.2.2.2.trans ht⟩

/-- For `t ≥ T0` and a `T0`-cover `P`: `compCount d univ t ≤ compCount d P t`. -/
theorem compCount_univ_le_net (d : Fin n → Fin n → ℝ) (hsymm : ∀ x y, d x y = d y x)
    (P : Finset (Fin n)) (T0 t : ℝ) (hcov : ∀ u, ∃ p ∈ P, d u p ≤ T0) (ht : T0 ≤ t) :
    compCount d univ t ≤ compCount d P t := by
  unfold compCount
  have e : (univ : Finset (Fin n)).image (thrGraph d univ t).connectedComponentMk =
      P.image (thrGraph d univ t).connectedComponentMk := by
    ext c
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨p, hp, hup⟩ := hcov u
      refine ⟨p, hp, ?_⟩
      rw [SimpleGraph.ConnectedComponent.eq]
      exact (thr_reach_of_close d hsymm univ t (mem_univ p) (mem_univ u)
        (by rw [hsymm]; linarith))
    · rintro ⟨p, _, rfl⟩; exact ⟨p, rfl⟩
  rw [e]
  apply card_image_le_of_factor
  intro a _ b _ hab
  rw [SimpleGraph.ConnectedComponent.eq] at hab ⊢
  exact hab.mono (thrGraph_mono d hsymm (subset_univ P) le_rfl)

/-- For `t ≥ 0`, `T0 ≥ 0` and a `T0`-cover `P`: `compCount d P (t + 2 T0) ≤ compCount d univ t`. -/
theorem compCount_net_le_univ (d : Fin n → Fin n → ℝ) (hsymm : ∀ x y, d x y = d y x)
    (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (P : Finset (Fin n)) (T0 t : ℝ) (hcov : ∀ u, ∃ p ∈ P, d u p ≤ T0) (hT0 : 0 ≤ T0)
    (ht : 0 ≤ t) :
    compCount d P (t + 2 * T0) ≤ compCount d univ t := by
  choose ρ hρP hρd using hcov
  unfold compCount
  set G' := thrGraph d P (t + 2 * T0)
  have e : P.image G'.connectedComponentMk =
      (univ : Finset (Fin n)).image (fun u => G'.connectedComponentMk (ρ u)) := by
    ext c
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, ?_⟩
      rw [SimpleGraph.ConnectedComponent.eq]
      exact thr_reach_of_close d hsymm P _ (hρP p) hp (by rw [hsymm]; linarith [hρd p])
    · rintro ⟨u, rfl⟩; exact ⟨ρ u, hρP u, rfl⟩
  rw [e]
  apply card_image_le_of_factor
  intro a _ b _ hab
  rw [SimpleGraph.ConnectedComponent.eq] at hab ⊢
  rw [SimpleGraph.reachable_iff_reflTransGen] at hab ⊢
  refine Relation.ReflTransGen.lift' ρ ?_ a b hab
  intro x y hxy
  rw [thrGraph_adj_iff d hsymm] at hxy
  show Relation.ReflTransGen G'.Adj (ρ x) (ρ y)
  rw [← SimpleGraph.reachable_iff_reflTransGen]
  apply thr_reach_of_close d hsymm P _ (hρP x) (hρP y)
  have h1 := htri (ρ x) x (ρ y)
  have h2 := htri x y (ρ y)
  have h3 := hρd x
  have h4 := hρd y
  rw [hsymm (ρ x) x] at h1
  linarith [hxy.2.2.2]

/-- Representatives of the components of the threshold graph on `Q` are pairwise `> t`. -/
theorem exists_sep_reps (d : Fin n → Fin n → ℝ) (hsymm : ∀ x y, d x y = d y x)
    (Q : Finset (Fin n)) (t : ℝ) :
    ∃ R : Finset (Fin n), R ⊆ Q ∧ R.card = compCount d Q t ∧
      ∀ a ∈ R, ∀ b ∈ R, a ≠ b → t < d a b := by
  set mk := (thrGraph d Q t).connectedComponentMk
  rcases Q.eq_empty_or_nonempty with rfl | ⟨a0, _⟩
  · refine ⟨∅, by simp, by simp [compCount], by simp⟩
  have : Nonempty (Fin n) := ⟨a0⟩
  have key : ∀ c ∈ Q.image mk, ∃ a ∈ Q, mk a = c := fun c hc => by simpa using hc
  choose! sec hsec hsec' using key
  refine ⟨(Q.image mk).image sec, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hx
    exact hsec c hc
  · unfold compCount
    apply Finset.card_image_of_injOn
    intro c hc c' hc' he
    have := congrArg mk he
    rwa [hsec' c hc, hsec' c' hc'] at this
  · intro a ha b hb hab
    obtain ⟨c, hc, rfl⟩ := mem_image.mp ha
    obtain ⟨c', hc', rfl⟩ := mem_image.mp hb
    by_contra hle
    push Not at hle
    have hr := thr_reach_of_close d hsymm Q t (hsec c hc) (hsec c' hc') hle
    have : mk (sec c) = mk (sec c') := SimpleGraph.ConnectedComponent.eq.mpr hr
    rw [hsec' c hc, hsec' c' hc'] at this
    exact hab (by rw [this])

lemma compSize_mono (d : Fin n → Fin n → ℝ) (hsymm : ∀ x y, d x y = d y x)
    (Q : Finset (Fin n)) {t t' : ℝ} (ht : t ≤ t') (v : Fin n) :
    compSize d Q t v ≤ compSize d Q t' v := by
  unfold compSize
  apply Finset.card_le_card
  intro u hu
  simp only [mem_filter] at hu ⊢
  exact ⟨hu.1, hu.2.mono (thrGraph_mono d hsymm subset_rfl ht)⟩

lemma one_le_compSize (d : Fin n → Fin n → ℝ) (Q : Finset (Fin n)) (t : ℝ) {v : Fin n}
    (hv : v ∈ Q) : 1 ≤ compSize d Q t v := by
  unfold compSize
  apply Finset.card_pos.mpr
  exact ⟨v, mem_filter.mpr ⟨hv, SimpleGraph.Reachable.refl v⟩⟩

lemma compSize_le (d : Fin n → Fin n → ℝ) (Q : Finset (Fin n)) (t : ℝ) (v : Fin n) :
    compSize d Q t v ≤ n := by
  unfold compSize
  calc _ ≤ (univ : Finset (Fin n)).card := card_le_card (subset_univ _)
    _ = n := by simp

/-- `compCount d univ t = Σ_v 1 / compSize d univ t v`. -/
theorem sum_inv_compSize (d : Fin n → Fin n → ℝ) (t : ℝ) :
    ∑ v : Fin n, (1 / (compSize d univ t v : ℝ)) = compCount d univ t := by
  set mk := (thrGraph d univ t).connectedComponentMk
  unfold compCount
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ.image mk) (g := mk)
    (fun x _ => mem_image_of_mem mk (mem_univ x))]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro c hc
  have hfib : ∀ v ∈ (univ : Finset (Fin n)).filter (fun v => mk v = c),
      compSize d univ t v = ((univ : Finset (Fin n)).filter (fun v => mk v = c)).card := by
    intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    unfold compSize
    congr 1
    apply Finset.filter_congr
    intro u _
    rw [← hv]
    exact ⟨fun h => (SimpleGraph.ConnectedComponent.eq.mpr h).symm,
      fun h => SimpleGraph.ConnectedComponent.eq.mp h.symm⟩
  rw [Finset.sum_congr rfl (fun v hv => by rw [hfib v hv])]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hne : ((univ : Finset (Fin n)).filter (fun v => mk v = c)).card ≠ 0 := by
    obtain ⟨v, _, hv⟩ := mem_image.mp hc
    exact Finset.card_ne_zero.mpr ⟨v, by simp [hv]⟩
  push_cast
  field_simp

end MTSPMst

end

section

/-!
Layer-cake for finite lists and the coarse comparison lemma.

`cnt L t = #{x ∈ L : t < x}`.
-/

open scoped Classical
open MeasureTheory Set

namespace MTSPMst

/-- Number of entries of `L` strictly above `t`. -/
noncomputable def cnt (L : List ℝ) (t : ℝ) : ℝ := ((L.filter (fun x => decide (t < x))).length : ℝ)

lemma cnt_nonneg (L : List ℝ) (t : ℝ) : 0 ≤ cnt L t := by unfold cnt; positivity

lemma cnt_antitone (L : List ℝ) : Antitone (cnt L) := by
  intro t t' htt
  unfold cnt
  have : List.Sublist (L.filter (fun x => decide (t' < x))) (L.filter (fun x => decide (t < x))) :=
    List.monotone_filter_right L (fun a h => by simp at h ⊢; linarith)
  exact_mod_cast this.length_le

lemma cnt_cons (x : ℝ) (L : List ℝ) (t : ℝ) :
    cnt (x :: L) t = (if t < x then 1 else 0) + cnt L t := by
  unfold cnt
  rw [List.filter_cons]
  split_ifs with h1 h2 h2 <;> simp_all [add_comm]

lemma cnt_eq_zero (L : List ℝ) (t : ℝ) (h : ∀ x ∈ L, x ≤ t) : cnt L t = 0 := by
  unfold cnt
  have : L.filter (fun x => decide (t < x)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx; simp only [decide_eq_true_eq, not_lt]; exact h x hx
  simp [this]

lemma ind_antitone (x : ℝ) : Antitone (fun t : ℝ => if t < x then (1 : ℝ) else 0) := by
  intro t t' htt
  simp only
  split_ifs <;> first | (exfalso; linarith) | norm_num

lemma integral_const_on_Ioo {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (h : ∀ t ∈ Ioo a b, f t = c) :
    ∫ t in a..b, f t = (b - a) * c := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo h, setIntegral_const, Real.volume_real_Ioo_of_le hab,
    smul_eq_mul]

lemma integral_ind {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    ∫ t in a..b, (if t < x then (1 : ℝ) else 0) = min (max (x - a) 0) (b - a) := by
  have hint : ∀ a' b', IntervalIntegrable (fun t : ℝ => if t < x then (1 : ℝ) else 0) volume a' b' :=
    fun _ _ => (ind_antitone x).intervalIntegrable
  rcases le_or_gt x a with hxa | hxa
  · rw [integral_const_on_Ioo hab (c := 0) (fun t ht => by simp only [ht.1.le.trans' hxa |> fun h => (not_lt.mpr (hxa.trans ht.1.le)), if_false])]
    rw [max_eq_right (by linarith)]; simp [hab]
  rcases le_or_gt x b with hxb | hxb
  · rw [← intervalIntegral.integral_add_adjacent_intervals (hint a x) (hint x b)]
    rw [integral_const_on_Ioo hxa.le (c := 1) (fun t ht => by simp [ht.2])]
    rw [integral_const_on_Ioo hxb (c := 0) (fun t ht => by simp [not_lt.mpr ht.1.le])]
    rw [max_eq_left (by linarith), min_eq_left (by linarith)]; ring
  · rw [integral_const_on_Ioo hab (c := 1) (fun t ht => by simp [ht.2.trans hxb])]
    rw [max_eq_left (by linarith), min_eq_right (by linarith)]; ring

/-- Layer-cake for a list, general form. -/
lemma integral_cnt {a b : ℝ} (hab : a ≤ b) : ∀ L : List ℝ,
    ∫ t in a..b, cnt L t = (L.map (fun x => min (max (x - a) 0) (b - a))).sum
  | [] => by simp [cnt]
  | x :: L => by
    simp only [cnt_cons, List.map_cons, List.sum_cons]
    rw [intervalIntegral.integral_add (ind_antitone x).intervalIntegrable
      (cnt_antitone L).intervalIntegrable, integral_ind hab, integral_cnt hab L]

/-- Layer-cake: `Σ max (x - a) 0 = ∫_a^b #{x > t} dt` when `b` bounds the list. -/
lemma integral_cnt_of_le {a b : ℝ} (hab : a ≤ b) (L : List ℝ) (hL : ∀ x ∈ L, x ≤ b) :
    ∫ t in a..b, cnt L t = (L.map (fun x => max (x - a) 0)).sum := by
  rw [integral_cnt hab]
  congr 1
  apply List.map_congr_left
  intro x hx
  have := hL x hx
  apply min_eq_left
  rcases le_total (x - a) 0 with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-- From zero: `∫_0^T #{x > t} dt = Σ min x T` for a nonnegative list. -/
lemma integral_cnt_zero {T : ℝ} (hT : 0 ≤ T) (L : List ℝ) (hL : ∀ x ∈ L, 0 ≤ x) :
    ∫ t in (0 : ℝ)..T, cnt L t = (L.map (fun x => min x T)).sum := by
  rw [integral_cnt hT]
  congr 1
  apply List.map_congr_left
  intro x hx
  rw [sub_zero, sub_zero, max_eq_left (hL x hx)]

lemma le_bound (L : List ℝ) (x : ℝ) (hx : x ∈ L) : x ≤ (L.map abs).sum :=
  (le_abs_self x).trans (List.single_le_sum (fun y hy => by
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy; exact abs_nonneg z) _ (List.mem_map_of_mem hx))

lemma abs_sum_nonneg (L : List ℝ) : 0 ≤ (L.map abs).sum :=
  List.sum_nonneg (fun y hy => by obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy; exact abs_nonneg z)

/-- **Coarse comparison.** If `cnt A ≤ cnt B` on `[T, ∞)` and `cnt B (t + δ) ≤ cnt A t` there,
then `0 ≤ Σ_B (x - T)⁺ - Σ_A (x - T)⁺ ≤ δ * cnt B T`. -/
theorem coarse_compare (A B : List ℝ) (T δ : ℝ) (hT : 0 ≤ T) (hδ : 0 ≤ δ)
    (h1 : ∀ t, T ≤ t → cnt A t ≤ cnt B t) (h2 : ∀ t, T ≤ t → cnt B (t + δ) ≤ cnt A t) :
    0 ≤ (B.map (fun x => max (x - T) 0)).sum - (A.map (fun x => max (x - T) 0)).sum ∧
      (B.map (fun x => max (x - T) 0)).sum - (A.map (fun x => max (x - T) 0)).sum
        ≤ δ * cnt B T := by
  set b := T + δ + (A.map abs).sum + (B.map abs).sum with hb
  have hA := abs_sum_nonneg A
  have hB := abs_sum_nonneg B
  have hAb : ∀ x ∈ A, x ≤ b := fun x hx => by linarith [le_bound A x hx]
  have hBb : ∀ x ∈ B, x ≤ b := fun x hx => by linarith [le_bound B x hx]
  have hTb : T ≤ b := by linarith
  rw [← integral_cnt_of_le hTb A hAb, ← integral_cnt_of_le hTb B hBb]
  have iA := fun a' b' => (cnt_antitone A).intervalIntegrable (μ := volume) (a := a') (b := b')
  have iB := fun a' b' => (cnt_antitone B).intervalIntegrable (μ := volume) (a := a') (b := b')
  constructor
  · rw [sub_nonneg]
    exact intervalIntegral.integral_mono_on hTb (iA _ _) (iB _ _) (fun t ht => h1 t ht.1)
  · have hshift : ∫ t in T..b, cnt B (t + δ) = ∫ t in T + δ..b, cnt B t := by
      rw [intervalIntegral.integral_comp_add_right (fun t => cnt B t) δ]
      rw [← intervalIntegral.integral_add_adjacent_intervals (iB (T + δ) b) (iB b (b + δ))]
      have : ∫ t in b..b + δ, cnt B t = 0 := by
        rw [integral_const_on_Ioo (by linarith) (c := 0)
          (fun t ht => cnt_eq_zero B t (fun x hx => (hBb x hx).trans ht.1.le))]
        ring
      rw [this, add_zero]
    have hmono : ∫ t in T..b, cnt B (t + δ) ≤ ∫ t in T..b, cnt A t := by
      apply intervalIntegral.integral_mono_on hTb _ (iA _ _) (fun t ht => h2 t ht.1)
      exact ((cnt_antitone B).comp_monotone (fun x y h => by show x + δ ≤ y + δ; linarith)).intervalIntegrable
    have hsplit : ∫ t in T..b, cnt B t = (∫ t in T..T + δ, cnt B t) + ∫ t in T + δ..b, cnt B t :=
      (intervalIntegral.integral_add_adjacent_intervals (iB _ _) (iB _ _)).symm
    have hfirst : ∫ t in T..T + δ, cnt B t ≤ δ * cnt B T := by
      have := intervalIntegral.integral_mono_on (by linarith : T ≤ T + δ) (iB _ _)
        (intervalIntegrable_const (c := cnt B T)) (fun t ht => cnt_antitone B ht.1)
      rw [intervalIntegral.integral_const, smul_eq_mul] at this
      linarith
    linarith

end MTSPMst

end

section

/-!
Fine part: the per-vertex capped quantity `hcap` and `gfull v = ∫_0^{T1} dt / compSize`.
-/

open scoped Classical
open MeasureTheory Set

namespace MTSPMst
open Finset

variable {n : ℕ}

/-- `cap j = min (pmax L j) T1` for `j < n`, and `T1` for `j ≥ n`. -/
noncomputable def capF (n : ℕ) (T1 : ℝ) (L : List ℝ) (j : ℕ) : ℝ :=
  if j < n then min (pmax L j) T1 else T1

/-- The per-vertex capped quantity `Σ_{j<s} (1/(j+1)) (cap (j+1) - cap j)`. -/
noncomputable def hcap (n s : ℕ) (T1 : ℝ) (L : List ℝ) : ℝ :=
  ∑ j ∈ range s, (1 / ((j : ℝ) + 1)) * (capF n T1 L (j + 1) - capF n T1 L j)

/-- `gfull v = ∫_0^{T1} dt / compSize d univ t v`. -/
noncomputable def gfull (d : Fin n → Fin n → ℝ) (T1 : ℝ) (v : Fin n) : ℝ :=
  ∫ t in (0 : ℝ)..T1, 1 / (compSize d univ t v : ℝ)

lemma foldl_max_ge : ∀ (l : List ℝ) (a : ℝ), a ≤ l.foldl max a
  | [], _ => le_rfl
  | x :: l, a => (le_max_left a x).trans (foldl_max_ge l (max a x))

lemma pmax_nonneg (L : List ℝ) (j : ℕ) : 0 ≤ pmax L j := foldl_max_ge _ 0

/-- `1[compSize ≤ j]`. -/
noncomputable def indS (d : Fin n → Fin n → ℝ) (v : Fin n) (j : ℕ) (t : ℝ) : ℝ :=
  if compSize d univ t v ≤ j then 1 else 0

/-- `1[compSize ≤ s] / compSize`. -/
noncomputable def gS (d : Fin n → Fin n → ℝ) (s : ℕ) (v : Fin n) (t : ℝ) : ℝ :=
  if compSize d univ t v ≤ s then 1 / (compSize d univ t v : ℝ) else 0

section
variable (d : Fin n → Fin n → ℝ) (hsymm : ∀ x y, d x y = d y x)
include hsymm

lemma indS_antitone (v : Fin n) (j : ℕ) : Antitone (indS d v j) := by
  intro t t' htt
  have := compSize_mono d hsymm univ htt v
  unfold indS
  split_ifs with h1 h2 <;> first | omega | norm_num

lemma inv_compSize_antitone (v : Fin n) : Antitone (fun t => 1 / (compSize d univ t v : ℝ)) := by
  intro t t' htt
  have h := compSize_mono d hsymm univ htt v
  have h1 := one_le_compSize d univ t (mem_univ v)
  simp only
  apply one_div_le_one_div_of_le (by exact_mod_cast (by omega : 0 < compSize d univ t v))
  exact_mod_cast h

lemma gS_antitone (s : ℕ) (v : Fin n) : Antitone (gS d s v) := by
  intro t t' htt
  have h := compSize_mono d hsymm univ htt v
  have h1 := one_le_compSize d univ t (mem_univ v)
  unfold gS
  split_ifs with h2 h3
  · apply one_div_le_one_div_of_le (by exact_mod_cast (by omega : 0 < compSize d univ t v))
    exact_mod_cast h
  · omega
  · positivity
  · exact le_rfl

end

lemma gS_nonneg (d : Fin n → Fin n → ℝ) (s : ℕ) (v : Fin n) (t : ℝ) : 0 ≤ gS d s v t := by
  unfold gS; split_ifs <;> positivity

lemma gS_le_one (d : Fin n → Fin n → ℝ) (s : ℕ) (v : Fin n) (t : ℝ) : gS d s v t ≤ 1 := by
  have h1 := one_le_compSize d univ t (mem_univ v)
  unfold gS; split_ifs
  · rw [div_le_one (by exact_mod_cast (by omega : 0 < compSize d univ t v))]
    exact_mod_cast h1
  · norm_num

lemma integral_indS (d : Fin n → Fin n → ℝ) (v : Fin n) {T1 : ℝ} (hT1 : 0 ≤ T1) (s : ℕ)
    (L : List ℝ)
    (hL : ∀ t : ℝ, 0 ≤ t → ∀ j ≤ s, j < n → (j + 1 ≤ compSize d univ t v ↔ pmax L j ≤ t))
    (j : ℕ) (hj : j ≤ s) :
    ∫ t in (0 : ℝ)..T1, indS d v j t = capF n T1 L j := by
  unfold capF
  split_ifs with hjn
  · rw [intervalIntegral.integral_congr (g := fun t => if t < pmax L j then (1 : ℝ) else 0)]
    · rw [integral_ind hT1, sub_zero, sub_zero, max_eq_left (pmax_nonneg L j)]
    · intro t ht
      rw [uIcc_of_le hT1] at ht
      have := hL t ht.1 j hj hjn
      unfold indS
      simp only
      congr 1
      apply propext
      rw [← not_le, ← this]
      omega
  · rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
    · simp
    · intro t _
      unfold indS
      have := compSize_le d univ t v
      simp only
      rw [if_pos (by omega)]

lemma telescope_inv (m : ℕ) (hm : 1 ≤ m) : ∀ s : ℕ,
    ∑ j ∈ range s, (1 / ((j : ℝ) + 1)) *
      ((if m ≤ j + 1 then (1 : ℝ) else 0) - (if m ≤ j then 1 else 0)) =
      if m ≤ s then 1 / (m : ℝ) else 0
  | 0 => by simp; omega
  | s + 1 => by
    rw [sum_range_succ, telescope_inv m hm s]
    by_cases h1 : m ≤ s
    · simp only [h1, if_true, show m ≤ s + 1 by omega]; ring
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : m = s + 1
      · subst h2; simp
      · rw [if_neg (by omega), if_neg (by omega)]; ring

/-- `hcap = ∫_0^{T1} 1[compSize ≤ s] / compSize`. -/
theorem hcap_eq_integral (d : Fin n → Fin n → ℝ) (hsymm : ∀ x y, d x y = d y x) (v : Fin n)
    {T1 : ℝ} (hT1 : 0 ≤ T1) (s : ℕ) (L : List ℝ)
    (hL : ∀ t : ℝ, 0 ≤ t → ∀ j ≤ s, j < n → (j + 1 ≤ compSize d univ t v ↔ pmax L j ≤ t)) :
    hcap n s T1 L = ∫ t in (0 : ℝ)..T1, gS d s v t := by
  have hfun : gS d s v = fun t => ∑ j ∈ range s,
      (1 / ((j : ℝ) + 1)) * (indS d v (j + 1) t - indS d v j t) := by
    funext t
    unfold gS indS
    rw [telescope_inv _ (one_le_compSize d univ t (mem_univ v)) s]
  rw [hfun, intervalIntegral.integral_finsetSum]
  · unfold hcap
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      (indS_antitone d hsymm v _).intervalIntegrable (indS_antitone d hsymm v _).intervalIntegrable,
      integral_indS d v hT1 s L hL (j + 1) (by omega), integral_indS d v hT1 s L hL j (by omega)]
  · intro j _
    exact ((indS_antitone d hsymm v _).intervalIntegrable.sub
      (indS_antitone d hsymm v _).intervalIntegrable).const_mul _

/-- `0 ≤ hcap ≤ T1`. -/
theorem hcap_bounds (d : Fin n → Fin n → ℝ) (hsymm : ∀ x y, d x y = d y x) (v : Fin n)
    {T1 : ℝ} (hT1 : 0 ≤ T1) (s : ℕ) (L : List ℝ)
    (hL : ∀ t : ℝ, 0 ≤ t → ∀ j ≤ s, j < n → (j + 1 ≤ compSize d univ t v ↔ pmax L j ≤ t)) :
    0 ≤ hcap n s T1 L ∧ hcap n s T1 L ≤ T1 := by
  rw [hcap_eq_integral d hsymm v hT1 s L hL]
  have hi := (gS_antitone d hsymm s v).intervalIntegrable (μ := volume) (a := 0) (b := T1)
  constructor
  · have := intervalIntegral.integral_mono_on hT1 (intervalIntegrable_const (c := (0 : ℝ))) hi
      (fun t _ => gS_nonneg d s v t)
    simpa using this
  · have := intervalIntegral.integral_mono_on hT1 hi (intervalIntegrable_const (c := (1 : ℝ)))
      (fun t _ => gS_le_one d s v t)
    simpa using this

/-- **Fine identity.** `Σ_v gfull v = T1 + Σ_{w ∈ W} min w T1`. -/
theorem sum_gfull (d : Fin n → Fin n → ℝ) (hsymm : ∀ x y, d x y = d y x) {T1 : ℝ}
    (hT1 : 0 ≤ T1) (W : List ℝ) (hW0 : ∀ w ∈ W, 0 ≤ w)
    (hWc : ∀ t : ℝ, 0 ≤ t → (W.filter (t < ·)).length + 1 = compCount d univ t) :
    ∑ v, gfull d T1 v = T1 + (W.map (fun w => min w T1)).sum := by
  unfold gfull
  rw [← intervalIntegral.integral_finsetSum
    (fun v _ => (inv_compSize_antitone d hsymm v).intervalIntegrable)]
  rw [intervalIntegral.integral_congr (g := fun t => 1 + cnt W t)]
  · rw [intervalIntegral.integral_add intervalIntegrable_const
      (cnt_antitone W).intervalIntegrable, integral_cnt_zero hT1 W hW0]
    simp
  · intro t ht
    rw [uIcc_of_le hT1] at ht
    simp only
    rw [sum_inv_compSize, ← hWc t ht.1, cnt]
    push_cast; ring

theorem gfull_sub_hcap_nonneg (d : Fin n → Fin n → ℝ) (hsymm : ∀ x y, d x y = d y x)
    (v : Fin n) {T1 : ℝ} (hT1 : 0 ≤ T1) (s : ℕ) (L : List ℝ)
    (hL : ∀ t : ℝ, 0 ≤ t → ∀ j ≤ s, j < n → (j + 1 ≤ compSize d univ t v ↔ pmax L j ≤ t)) :
    0 ≤ gfull d T1 v - hcap n s T1 L := by
  rw [hcap_eq_integral d hsymm v hT1 s L hL, gfull, sub_nonneg]
  apply intervalIntegral.integral_mono_on hT1 (gS_antitone d hsymm s v).intervalIntegrable
    (inv_compSize_antitone d hsymm v).intervalIntegrable
  intro t _
  unfold gS; split_ifs
  · exact le_rfl
  · positivity

theorem sum_gfull_sub_hcap_le (d : Fin n → Fin n → ℝ) (hsymm : ∀ x y, d x y = d y x)
    {T1 : ℝ} (hT1 : 0 ≤ T1) (s : ℕ) (hs : 1 ≤ s) (Lv : Fin n → List ℝ)
    (hL : ∀ v, ∀ t : ℝ, 0 ≤ t → ∀ j ≤ s, j < n →
      (j + 1 ≤ compSize d univ t v ↔ pmax (Lv v) j ≤ t)) :
    ∑ v, (gfull d T1 v - hcap n s T1 (Lv v)) ≤ n * T1 / s := by
  have e : ∀ v, gfull d T1 v - hcap n s T1 (Lv v) =
      ∫ t in (0 : ℝ)..T1, (1 / (compSize d univ t v : ℝ) - gS d s v t) := by
    intro v
    rw [hcap_eq_integral d hsymm v hT1 s (Lv v) (hL v), gfull, intervalIntegral.integral_sub
      (inv_compSize_antitone d hsymm v).intervalIntegrable
      (gS_antitone d hsymm s v).intervalIntegrable]
  simp_rw [e]
  rw [← intervalIntegral.integral_finsetSum (fun v _ =>
    (inv_compSize_antitone d hsymm v).intervalIntegrable.sub
      (gS_antitone d hsymm s v).intervalIntegrable)]
  have hsum : IntervalIntegrable
      (fun t => ∑ v, (1 / (compSize d univ t v : ℝ) - gS d s v t)) volume 0 T1 := by
    have := IntervalIntegrable.sum (μ := volume) (a := 0) (b := T1) (univ : Finset (Fin n))
      (f := fun v t => 1 / (compSize d univ t v : ℝ) - gS d s v t) (fun v _ =>
      (inv_compSize_antitone d hsymm v).intervalIntegrable.sub
        (gS_antitone d hsymm s v).intervalIntegrable)
    have e2 : (fun t => ∑ v, (1 / (compSize d univ t v : ℝ) - gS d s v t)) =
        ∑ v, (fun t => 1 / (compSize d univ t v : ℝ) - gS d s v t) := by
      funext t; simp [Finset.sum_apply]
    rw [e2]; exact this
  have hb := intervalIntegral.integral_mono_on hT1 hsum
    (intervalIntegrable_const (c := (n : ℝ) / s)) (a := 0) (b := T1) (μ := volume) (by
      intro t _
      calc ∑ v, (1 / (compSize d univ t v : ℝ) - gS d s v t) ≤ ∑ _v : Fin n, (1 / (s : ℝ)) := by
            apply sum_le_sum
            intro v _
            unfold gS
            split_ifs with h
            · rw [sub_self]; positivity
            · rw [sub_zero]
              apply one_div_le_one_div_of_le (by exact_mod_cast hs)
              exact_mod_cast (by omega : s ≤ compSize d univ t v)
        _ = n / s := by simp [div_eq_mul_inv])
  rw [intervalIntegral.integral_const, smul_eq_mul] at hb
  calc _ ≤ (T1 - 0) * (n / s) := hb
    _ = n * T1 / s := by ring

end MTSPMst

end

section

open scoped Classical

namespace MTSPDecode
open SublinearSteiner

/-- MSB-first decoding of `m` bits starting at position `i*m`. -/
def dec (m : ℕ) (t : ℕ → Bool) (i : ℕ) : ℕ :=
  ∑ b ∈ Finset.range m, if t (i * m + b) then 2 ^ (m - 1 - b) else 0

/-- Bits (MSB first) to numbers. -/
def bitsEquiv (m : ℕ) : (Fin m → Bool) ≃ Fin (2 ^ m) :=
  ((Equiv.arrowCongr Fin.revPerm finTwoEquiv.symm)).trans finFunctionFinEquiv

lemma bitsEquiv_val (m : ℕ) (g : Fin m → Bool) :
    ((bitsEquiv m g : Fin (2 ^ m)) : ℕ) = ∑ b : Fin m, if g b then 2 ^ (m - 1 - (b : ℕ)) else 0 := by
  simp only [bitsEquiv, Equiv.trans_apply, finFunctionFinEquiv_apply, Equiv.arrowCongr_apply]
  rw [← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Function.comp_apply, Fin.revPerm_apply, Fin.revPerm_symm, Fin.rev_rev, Fin.val_rev]
  cases g b <;> simp [finTwoEquiv] <;> omega

lemma dec_lt (m : ℕ) (t : ℕ → Bool) (i : ℕ) : dec m t i < 2 ^ m := by
  have h := (bitsEquiv m (fun b => t (i * m + b))).isLt
  rw [bitsEquiv_val] at h
  unfold dec
  rw [Finset.sum_range]
  exact h

/-- Counting tapes through the decoded tuple. -/
theorem tape_count (r m B : ℕ) (hB : r * m ≤ B) (G : (ℕ → ℕ) → Prop)
    (hG : ∀ v v' : ℕ → ℕ, (∀ i < r, v i = v' i) → (G v ↔ G v')) :
    ((Finset.univ.filter (fun t : Fin B → Bool => G (dec m (extendTape t)))).card : ℝ) =
      2 ^ (B - r * m) * ((Finset.univ.filter (fun u : Fin r → Fin (2 ^ m) =>
        G (fun i => if h : i < r then (u ⟨i, h⟩ : ℕ) else 0))).card : ℝ) := by
  obtain ⟨D, rfl⟩ : ∃ D, B = r * m + D := ⟨B - r * m, by omega⟩
  let e1 : (Fin (r * m + D) → Bool) ≃ (Fin (r * m) → Bool) × (Fin D → Bool) :=
    (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _)
  have he1 : ∀ t (j : Fin (r * m)), (e1 t).1 j = t (Fin.castAdd D j) := by
    intro t j; simp [e1, Equiv.arrowCongr]
  let e2 : (Fin (r * m) → Bool) ≃ (Fin r → Fin (2 ^ m)) :=
    ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)).trans
      (Equiv.arrowCongr (Equiv.refl _) (bitsEquiv m))
  have he2 : ∀ (a : Fin (r * m) → Bool) (i : Fin r),
      ((e2 a i : Fin (2 ^ m)) : ℕ) =
        ∑ b : Fin m, if a (finProdFinEquiv (i, b)) then 2 ^ (m - 1 - (b : ℕ)) else 0 := by
    intro a i
    simp only [e2, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl,
      Function.comp_apply, id]
    rw [bitsEquiv_val]
    rfl
  have hdec : ∀ t : Fin (r * m + D) → Bool, ∀ i (hi : i < r),
      dec m (extendTape t) i = ((e2 (e1 t).1 ⟨i, hi⟩ : Fin (2 ^ m)) : ℕ) := by
    intro t i hi
    rw [he2]
    unfold dec
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro b _
    have hlt : i * m + b < r * m := by
      have := b.isLt
      calc i * m + b < i * m + m := by omega
        _ = (i + 1) * m := by ring
        _ ≤ r * m := Nat.mul_le_mul_right _ hi
    have hlt2 : i * m + b < r * m + D := by omega
    rw [he1]
    have : (Fin.castAdd D (finProdFinEquiv ((⟨i, hi⟩ : Fin r), b)) : Fin (r * m + D)) =
        ⟨i * m + b, hlt2⟩ := by
      ext; simp [finProdFinEquiv]; ring
    rw [this]
    simp [extendTape, hlt2]
  have key : ∀ t : Fin (r * m + D) → Bool,
      (G (dec m (extendTape t)) ↔ G (fun i => if h : i < r then ((e2 (e1 t).1 ⟨i, h⟩ : Fin (2 ^ m)) : ℕ) else 0)) := by
    intro t
    apply hG
    intro i hi
    rw [dif_pos hi, hdec t i hi]
  have hcard : (Finset.univ.filter (fun t : Fin (r * m + D) → Bool => G (dec m (extendTape t)))).card =
      ((Finset.univ.filter (fun u : Fin r → Fin (2 ^ m) =>
        G (fun i => if h : i < r then (u ⟨i, h⟩ : ℕ) else 0))) ×ˢ
        (Finset.univ : Finset (Fin D → Bool))).card := by
    apply Finset.card_nbij' (fun t => (e2 (e1 t).1, (e1 t).2)) (fun p => e1.symm (e2.symm p.1, p.2))
    · intro t ht
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht
      simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and,
        Finset.coe_univ, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_univ, and_true]
      exact (key t).mp ht
    · intro p hp
      simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and,
        Finset.coe_univ, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_univ, and_true] at hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      rw [key]; simpa using hp
    · intro t _; simp
    · intro p _; simp
  rw [hcard, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  push_cast
  rw [show r * m + D - r * m = D by omega]
  ring

end MTSPDecode

end

section

/-! Mathematical specification of the estimator program (mirrors the code exactly). -/

open scoped Classical

namespace MTSPEst
open MTSPMst Finset

/-! Integer parameters. -/

lemma qOf_ex (n : ℕ) : ∃ q, 1 ≤ q ∧ n ≤ q ^ 4 :=
  ⟨n + 1, by omega, le_trans (Nat.le_succ n) (Nat.le_self_pow (by norm_num) _)⟩

/-- Least `q ≥ 1` with `n ≤ q^4`. -/
noncomputable def qOf (n : ℕ) : ℕ := Nat.find (qOf_ex n)

lemma qOf_pos (n : ℕ) : 1 ≤ qOf n := (Nat.find_spec (qOf_ex n)).1
lemma qOf_spec (n : ℕ) : n ≤ qOf n ^ 4 := (Nat.find_spec (qOf_ex n)).2
lemma qOf_min (n q : ℕ) (h1 : 1 ≤ q) (hq : q < qOf n) : q ^ 4 < n := by
  have := Nat.find_min (qOf_ex n) hq
  push Not at this
  exact this h1

lemma qOf_le (n : ℕ) (hn : 1 ≤ n) : qOf n ≤ n :=
  Nat.find_min' (qOf_ex n) ⟨hn, Nat.le_self_pow (by norm_num) _⟩

lemma mOf_ex (n : ℕ) : ∃ m, n ≤ 2 ^ m := ⟨n, (Nat.lt_two_pow_self).le⟩

/-- Least `m` with `n ≤ 2^m`. -/
noncomputable def mOf (n : ℕ) : ℕ := Nat.find (mOf_ex n)

lemma mOf_spec (n : ℕ) : n ≤ 2 ^ mOf n := Nat.find_spec (mOf_ex n)
lemma mOf_min (n m : ℕ) (hm : m < mOf n) : 2 ^ m < n := by
  have := Nat.find_min (mOf_ex n) hm
  omega
lemma mOf_le (n : ℕ) : mOf n ≤ n := Nat.find_min' (mOf_ex n) (Nat.lt_two_pow_self).le

noncomputable def kOf (K1 n : ℕ) : ℕ := min n (K1 * qOf n ^ 3)
noncomputable def sOf (S1 n : ℕ) : ℕ := S1 * qOf n
noncomputable def rOf (R1 n : ℕ) : ℕ := R1 * qOf n ^ 2
/-- Size of the memory regions. -/
noncomputable def LOf (S1 n : ℕ) : ℕ := n + sOf S1 n

/-! Real quantities. -/

variable {n : ℕ}

def allOnes : Fin n → Bool := fun _ => true

/-- Farthest-first run. -/
noncomputable def run1 (K1 : ℕ) (d : Fin n → Fin n → ℝ) (h : 0 < n) :
    GState n × List (Fin n × ℝ) :=
  grun d true allOnes ⟨0, h⟩ (kOf K1 n - 1)

noncomputable def keyN (g : GState n) (u : ℕ) : ℝ := if h : u < n then g.key ⟨u, h⟩ else 0

/-- `T0 = max (0, max_u key u)` of the farthest-first run (left fold over `u = 0, …, n-1`). -/
noncomputable def T0 (K1 : ℕ) (d : Fin n → Fin n → ℝ) (h : 0 < n) : ℝ :=
  (List.range n).foldl (fun a u => max a (keyN (run1 K1 d h).1 u)) 0

noncomputable def T1 (K1 : ℕ) (cinv : ℚ) (d : Fin n → Fin n → ℝ) (h : 0 < n) : ℝ :=
  T0 K1 d h * (cinv : ℝ)

/-- The net: `0` and the recorded vertices of the farthest-first run. -/
noncomputable def netP (K1 : ℕ) (d : Fin n → Fin n → ℝ) (h : 0 < n) : Fin n → Bool :=
  fun u => decide ((u : ℕ) = 0 ∨ u ∈ (run1 K1 d h).2.map Prod.fst)

noncomputable def run2 (K1 : ℕ) (d : Fin n → Fin n → ℝ) (h : 0 < n) :
    GState n × List (Fin n × ℝ) :=
  grun d false (netP K1 d h) ⟨0, h⟩ (kOf K1 n - 1)

/-- Recorded values of the Prim run on the net. -/
noncomputable def U (K1 : ℕ) (d : Fin n → Fin n → ℝ) (h : 0 < n) : List ℝ :=
  (run2 K1 d h).2.map Prod.snd

noncomputable def A' (K1 : ℕ) (cinv : ℚ) (d : Fin n → Fin n → ℝ) (h : 0 < n) : ℝ :=
  ∑ j ∈ range (U K1 d h).length, max ((U K1 d h).getD j 0 - T1 K1 cinv d h) 0

noncomputable def run3 (S1 : ℕ) (d : Fin n → Fin n → ℝ) (v : Fin n) :
    GState n × List (Fin n × ℝ) :=
  grun d false allOnes v (sOf S1 n)

/-- Per-sample quantity, in terms of `MTSPMst.hcap` (`MTSPMst.capF`). -/
noncomputable def hcap (K1 S1 : ℕ) (cinv : ℚ) (d : Fin n → Fin n → ℝ) (h : 0 < n) (v : Fin n) : ℝ :=
  MTSPMst.hcap n (sOf S1 n) (T1 K1 cinv d h) ((run3 S1 d v).2.map Prod.snd)

noncomputable def X (K1 S1 : ℕ) (cinv : ℚ) (d : Fin n → Fin n → ℝ) (h : 0 < n) (u : ℕ) : ℝ :=
  if hu : u < n then MTSPEst.hcap K1 S1 cinv d h ⟨u, hu⟩ else 0

/-- The output of the estimator, given the sampled vertices `u i`
(in the theorem, `u = MTSPDecode.dec (mOf n) f`). -/
noncomputable def estOut (K1 S1 R1 : ℕ) (cinv scale : ℚ) (d : Fin n → Fin n → ℝ) (u : ℕ → ℕ) : ℝ :=
  if h : n ≤ 1 then 0 else
    (A' K1 cinv d (by omega) + ((2 : ℝ) ^ mOf n / (rOf R1 n : ℝ)) *
        ∑ i ∈ range (rOf R1 n), X K1 S1 cinv d (by omega) (u i) - T1 K1 cinv d (by omega)) *
      (scale : ℝ)

/-! Helper lemmas. -/

/-- Partial decode. -/
def dpart (t : ℕ → Bool) (base k : ℕ) : ℕ :=
  ∑ b ∈ range k, if t (base + b) then 2 ^ (k - 1 - b) else 0

lemma dpart_zero (t : ℕ → Bool) (base : ℕ) : dpart t base 0 = 0 := by simp [dpart]

lemma dpart_succ (t : ℕ → Bool) (base k : ℕ) :
    dpart t base (k + 1) = 2 * dpart t base k + (if t (base + k) then 1 else 0) := by
  unfold dpart
  rw [sum_range_succ, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro b hb
    have hb' := mem_range.mp hb
    split_ifs
    · rw [show k + 1 - 1 - b = (k - 1 - b) + 1 by omega, pow_succ]; ring
    · simp
  · simp

lemma decode_eq (m : ℕ) (t : ℕ → Bool) (i : ℕ) : MTSPDecode.dec m t i = dpart t (i * m) m := rfl

lemma pmax_zero (L : List ℝ) : pmax L 0 = 0 := by simp [pmax]

lemma pmax_succ (L : List ℝ) (j : ℕ) :
    pmax L (j + 1) = if j < L.length then max (pmax L j) (L.getD j 0) else pmax L j := by
  unfold pmax
  rw [List.take_add_one]
  split_ifs with h
  · rw [List.getElem?_eq_getElem h, List.getD_eq_getElem _ _ h, List.foldl_append]
    rfl
  · rw [List.getElem?_eq_none (by omega)]
    simp

lemma foldl_range_succ (g : ℝ → ℕ → ℝ) (a : ℝ) (k : ℕ) :
    (List.range (k + 1)).foldl g a = g ((List.range k).foldl g a) k := by
  rw [List.range_succ, List.foldl_append]; rfl

end MTSPEst

end

section

/-! Verification of the blocks after the first call. -/

open scoped Classical

namespace MTSPEst
open SublinearSteiner SmaleNinth Finset

variable {Q : Program} {n : ℕ} {d : Fin n → Fin n → ℝ} {f : ℕ → Bool}

theorem t0_run (b : ℕ) (hE : Emb Q b (t0Code b)) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (KB : ℤ) (keyf : ℕ → ℝ) (h1 : S.cfg.ptrs 1 = n) (h9 : S.cfg.ptrs 9 = KB)
    (hkey : ∀ u : ℕ, u < n → S.cfg.mem (KB + u) = keyf u) :
    Reach Q d f (n * 8 + 4) S (fun S' => S'.cfg.pc = b + 11 ∧ Fr S S' [20, 21] [4, 5, 6] ∧
      S'.cfg.regs 4 = (List.range n).foldl (fun a u => max a (keyf u)) 0) := by
  have q0 : Q[b]? = some (.core (.const 4 ((0 : ℚ) : ℝ))) := emb_at0 hE (by simp [t0Code])
  have q1 : Q[b + 1]? = some (.core (.pset 20 0)) := hE 1 (by simp [t0Code])
  have q2 : Q[b + 2]? = some (.core (.pcopy 21 9)) := hE 2 (by simp [t0Code])
  have q3 : Q[b + 3]? = some (.core (.pjle 1 20 (b + 11))) := hE 3 (by simp [t0Code])
  have q4 : Q[b + 4]? = some (.core (.load 5 21)) := hE 4 (by simp [t0Code])
  have q5 : Q[b + 5]? = some (.core (.sub 6 5 4)) := hE 5 (by simp [t0Code])
  have q6 : Q[b + 6]? = some (.core (.jle 6 (b + 8))) := hE 6 (by simp [t0Code])
  have q7 : Q[b + 7]? = some (.core (.add 4 4 6)) := hE 7 (by simp [t0Code])
  have q8 : Q[b + 8]? = some (.core (.pinc 20)) := hE 8 (by simp [t0Code])
  have q9 : Q[b + 9]? = some (.core (.pinc 21)) := hE 9 (by simp [t0Code])
  have q10 : Q[b + 10]? = some (.core (.pjle 0 0 (b + 3))) := hE 10 (by simp [t0Code])
  let g : ℝ → ℕ → ℝ := fun a u => max a (keyf u)
  let Inv : ℕ → State → Prop := fun i S' =>
    S'.cfg.pc = b + 3 ∧ Fr S S' [20, 21] [4, 5, 6] ∧ S'.cfg.ptrs 20 = i ∧
      S'.cfg.ptrs 21 = KB + i ∧ S'.cfg.regs 4 = (List.range i).foldl g 0
  have h0 : Reach Q d f 3 S (Inv 0) := by
    apply reach_exact 3
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp (config := {contextual := true}) [step, ho, hpc, q0, q1, q2, RAMStep, List.getElem?_map,
      Instr.coreOf, Inv, State.next, h9, fr_iff (Fr.refl ho [20, 21] [4, 5, 6])]
  have hit : ∀ i < n, ∀ S', Inv i S' → Reach Q d f 8 S' (Inv (i + 1)) := by
    rintro i hi S' ⟨hpc', hF, h20, h21, h4⟩
    have h1' : S'.cfg.ptrs 1 = n := (hF.ptrs 1 (by decide)).trans h1
    have hm : S'.cfg.mem (KB + i) = keyf i := by rw [hF.mem]; exact hkey i hi
    have hi1 : ¬ n ≤ i := by omega
    have hi2 : ¬ (n : ℤ) ≤ i := by omega
    have ho' := hF.out
    simp only [Inv]
    rw [foldl_range_succ]
    generalize (List.range i).foldl g 0 = A at h4 ⊢
    by_cases hc : keyf i ≤ A
    · apply reach_mono (show 7 ≤ 8 by norm_num) (fun _ h => h)
      apply reach_exact 7
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      simp (config := {contextual := true}) [step, ho', hpc', q3, q4, q5, q6, q8, q9, q10, RAMStep,
        List.getElem?_map, Instr.coreOf, State.next, h1', h20, h21, h4, hm, hc, hi1, hi2, fr_iff hF, g]
      ring
    · apply reach_exact 8
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      simp (config := {contextual := true}) [step, ho', hpc', q3, q4, q5, q6, q7, q8, q9, q10, RAMStep,
        List.getElem?_map, Instr.coreOf, State.next, h1', h20, h21, h4, hm, hc, hi1, hi2, fr_iff hF, g]
      exact ⟨by ring, le_of_lt (lt_of_not_ge hc)⟩
  have hex : ∀ S', Inv n S' → Reach Q d f 1 S' (fun S' => S'.cfg.pc = b + 11 ∧
      Fr S S' [20, 21] [4, 5, 6] ∧ S'.cfg.regs 4 = (List.range n).foldl (fun a u => max a (keyf u)) 0) := by
    rintro S' ⟨hpc', hF, h20, h21, h4⟩
    have h1' : S'.cfg.ptrs 1 = n := (hF.ptrs 1 (by decide)).trans h1
    have ho' := hF.out
    apply reach_exact 1
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp [step, ho', hpc', q3, RAMStep, List.getElem?_map, Instr.coreOf, h1', h20, fr_iff hF]
    exact h4
  have := reach_bind h0 (reach_loop_exit n hit hex)
  exact reach_mono (by omega) (fun _ h => h) this

theorem t1_run (cinv : ℚ) (b : ℕ) (hE : Emb Q b (t1Code cinv)) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) :
    Reach Q d f 2 S (fun S' => S'.cfg.pc = b + 2 ∧ Fr S S' [] [1, 7] ∧
      S'.cfg.regs 1 = S.cfg.regs 4 * (cinv : ℝ)) := by
  have q0 : Q[b]? = some (.core (.const 7 (cinv : ℝ))) := emb_at0 hE (by simp [t1Code])
  have q1 : Q[b + 1]? = some (.core (.mul 1 4 7)) := hE 1 (by simp [t1Code])
  apply reach_exact 2
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q0, q1, RAMStep, List.getElem?_map,
    Instr.coreOf, State.next, fr_iff (Fr.refl ho [] [1, 7])]

/-- The marked integer memory. -/
def markI (I : ℤ → ℤ) (MB : ℤ) (vtx : ℕ → ℕ) (c : ℕ) : ℤ → ℤ :=
  fun z => if z = MB ∨ ∃ j, j < c ∧ z = MB + vtx j then 1 else I z

lemma markI_zero (I : ℤ → ℤ) (MB : ℤ) (vtx : ℕ → ℕ) :
    Function.update I MB 1 = markI I MB vtx 0 := by
  funext z; simp [markI, Function.update_apply]

lemma markI_succ (I : ℤ → ℤ) (MB : ℤ) (vtx : ℕ → ℕ) (c : ℕ) :
    Function.update (markI I MB vtx c) (MB + vtx c) 1 = markI I MB vtx (c + 1) := by
  funext z
  simp only [markI, Function.update_apply]
  by_cases h : z = MB + vtx c
  · simp only [h, if_true]
    rw [if_pos (Or.inr ⟨c, by omega, rfl⟩)]
  · rw [if_neg h]
    congr 1
    apply propext
    constructor
    · rintro (h' | ⟨j, hj, hj'⟩)
      · exact Or.inl h'
      · exact Or.inr ⟨j, by omega, hj'⟩
    · rintro (h' | ⟨j, hj, hj'⟩)
      · exact Or.inl h'
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · exact Or.inr ⟨j, hj, hj'⟩
        · subst hj; exact absurd hj' h

theorem mark_run (b : ℕ) (hE : Emb Q b (markCode b)) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (MB OV : ℤ) (cnt : ℕ) (vtx : ℕ → ℕ) (h11 : S.cfg.ptrs 11 = MB)
    (h12 : S.cfg.ptrs 12 = 1) (h16 : S.cfg.ptrs 16 = cnt) (h10 : S.cfg.ptrs 10 = OV)
    (hov : ∀ j, j < cnt → S.imem (OV + j) = vtx j)
    (hdis : ∀ j, j < cnt → OV + j ≠ MB ∧ ∀ j', j' < cnt → OV + j ≠ MB + vtx j') :
    Reach Q d f (cnt * 7 + 4) S (fun S' => S'.cfg.pc = b + 10 ∧ S'.output = none ∧
      (∀ j, j ∉ [20, 21, 27, 28] → S'.cfg.ptrs j = S.cfg.ptrs j) ∧ S'.cfg.regs = S.cfg.regs ∧
      S'.cfg.mem = S.cfg.mem ∧ S'.coins = S.coins ∧ S'.queries = S.queries ∧
      S'.imem = markI S.imem MB vtx cnt) := by
  have q0 : Q[b]? = some (.integerStore 11 12) := emb_at0 hE (by simp [markCode])
  have q1 : Q[b + 1]? = some (.core (.pset 20 0)) := hE 1 (by simp [markCode])
  have q2 : Q[b + 2]? = some (.core (.pcopy 21 10)) := hE 2 (by simp [markCode])
  have q3 : Q[b + 3]? = some (.core (.pjle 16 20 (b + 10))) := hE 3 (by simp [markCode])
  have q4 : Q[b + 4]? = some (.integerLoad 27 21) := hE 4 (by simp [markCode])
  have q5 : Q[b + 5]? = some (.pointerAdd 28 11 27) := hE 5 (by simp [markCode])
  have q6 : Q[b + 6]? = some (.integerStore 28 12) := hE 6 (by simp [markCode])
  have q7 : Q[b + 7]? = some (.core (.pinc 20)) := hE 7 (by simp [markCode])
  have q8 : Q[b + 8]? = some (.core (.pinc 21)) := hE 8 (by simp [markCode])
  have q9 : Q[b + 9]? = some (.core (.pjle 0 0 (b + 3))) := hE 9 (by simp [markCode])
  let Inv : ℕ → State → Prop := fun i S' =>
    S'.cfg.pc = b + 3 ∧ S'.output = none ∧
      (∀ j, j ∉ [20, 21, 27, 28] → S'.cfg.ptrs j = S.cfg.ptrs j) ∧ S'.cfg.regs = S.cfg.regs ∧
      S'.cfg.mem = S.cfg.mem ∧ S'.coins = S.coins ∧ S'.queries = S.queries ∧
      S'.imem = markI S.imem MB vtx i ∧ S'.cfg.ptrs 20 = i ∧ S'.cfg.ptrs 21 = OV + i
  have h0 : Reach Q d f 3 S (Inv 0) := by
    apply reach_exact 3
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp (config := {contextual := true}) [step, ho, hpc, q0, q1, q2, RAMStep, List.getElem?_map,
      Instr.coreOf, Inv, State.next, h10, h11, h12, Function.update_apply]
    rw [← markI_zero]
  have hit : ∀ i < cnt, ∀ S', Inv i S' → Reach Q d f 7 S' (Inv (i + 1)) := by
    rintro i hi S' ⟨hpc', ho', hp, hr, hm, hc, hq, hI, h20, h21⟩
    have h16' : S'.cfg.ptrs 16 = cnt := (hp 16 (by decide)).trans h16
    have h11' : S'.cfg.ptrs 11 = MB := (hp 11 (by decide)).trans h11
    have h12' : S'.cfg.ptrs 12 = 1 := (hp 12 (by decide)).trans h12
    have hv : S'.imem (OV + i) = vtx i := by
      rw [hI]; simp only [markI]
      rw [if_neg]
      · exact hov i hi
      · rintro (h | ⟨j, hj, h⟩)
        · exact (hdis i hi).1 h
        · exact (hdis i hi).2 j (by omega) h
    have hi1 : ¬ cnt ≤ i := by omega
    have hi2 : ¬ (cnt : ℤ) ≤ i := by omega
    apply reach_exact 7
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp (config := {contextual := true}) [step, ho', hpc', q3, q4, q5, q6, q7, q8, q9, RAMStep,
      List.getElem?_map, Instr.coreOf, State.next, h16', h20, h21, hv, h11', h12', hi1, hi2, Inv, hr,
      hm, hc, hq, Function.update_apply]
    refine ⟨fun j h1 h2 h3 h4 => ?_, ?_, by ring⟩
    · simp [h1, h2, h3, h4, hp j (by simp [h1, h2, h3, h4])]
    · rw [hI, ← markI_succ]
  have hex : ∀ S', Inv cnt S' → Reach Q d f 1 S' (fun S' => S'.cfg.pc = b + 10 ∧ S'.output = none ∧
      (∀ j, j ∉ [20, 21, 27, 28] → S'.cfg.ptrs j = S.cfg.ptrs j) ∧ S'.cfg.regs = S.cfg.regs ∧
      S'.cfg.mem = S.cfg.mem ∧ S'.coins = S.coins ∧ S'.queries = S.queries ∧
      S'.imem = markI S.imem MB vtx cnt) := by
    rintro S' ⟨hpc', ho', hp, hr, hm, hc, hq, hI, h20, h21⟩
    have h16' : S'.cfg.ptrs 16 = cnt := (hp 16 (by decide)).trans h16
    apply reach_exact 1
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp [step, ho', hpc', q3, RAMStep, List.getElem?_map, Instr.coreOf, h16', h20]
    exact ⟨fun j h1 h2 h3 h4 => hp j (by simp [h1, h2, h3, h4]), hr, hm, hc, hq, hI⟩
  have := reach_bind h0 (reach_loop_exit cnt hit hex)
  exact reach_mono (by omega) (fun _ h => h) this

theorem ap_run (b : ℕ) (hE : Emb Q b (apCode b)) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (OW : ℤ) (cnt : ℕ) (vals : ℕ → ℝ) (T : ℝ) (h17 : S.cfg.ptrs 17 = cnt)
    (h10 : S.cfg.ptrs 10 = OW) (h1 : S.cfg.regs 1 = T)
    (hval : ∀ j, j < cnt → S.cfg.mem (OW + j) = vals j) :
    Reach Q d f (cnt * 8 + 4) S (fun S' => S'.cfg.pc = b + 11 ∧ Fr S S' [20, 21] [2, 5, 6] ∧
      S'.cfg.regs 2 = ∑ j ∈ range cnt, max (vals j - T) 0) := by
  have q0 : Q[b]? = some (.core (.const 2 ((0 : ℚ) : ℝ))) := emb_at0 hE (by simp [apCode])
  have q1 : Q[b + 1]? = some (.core (.pset 20 0)) := hE 1 (by simp [apCode])
  have q2 : Q[b + 2]? = some (.core (.pcopy 21 10)) := hE 2 (by simp [apCode])
  have q3 : Q[b + 3]? = some (.core (.pjle 17 20 (b + 11))) := hE 3 (by simp [apCode])
  have q4 : Q[b + 4]? = some (.core (.load 5 21)) := hE 4 (by simp [apCode])
  have q5 : Q[b + 5]? = some (.core (.sub 6 5 1)) := hE 5 (by simp [apCode])
  have q6 : Q[b + 6]? = some (.core (.jle 6 (b + 8))) := hE 6 (by simp [apCode])
  have q7 : Q[b + 7]? = some (.core (.add 2 2 6)) := hE 7 (by simp [apCode])
  have q8 : Q[b + 8]? = some (.core (.pinc 20)) := hE 8 (by simp [apCode])
  have q9 : Q[b + 9]? = some (.core (.pinc 21)) := hE 9 (by simp [apCode])
  have q10 : Q[b + 10]? = some (.core (.pjle 0 0 (b + 3))) := hE 10 (by simp [apCode])
  let Inv : ℕ → State → Prop := fun i S' =>
    S'.cfg.pc = b + 3 ∧ Fr S S' [20, 21] [2, 5, 6] ∧ S'.cfg.ptrs 20 = i ∧
      S'.cfg.ptrs 21 = OW + i ∧ S'.cfg.regs 2 = ∑ j ∈ range i, max (vals j - T) 0
  have h0 : Reach Q d f 3 S (Inv 0) := by
    apply reach_exact 3
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp (config := {contextual := true}) [step, ho, hpc, q0, q1, q2, RAMStep, List.getElem?_map,
      Instr.coreOf, Inv, State.next, h10, fr_iff (Fr.refl ho [20, 21] [2, 5, 6])]
  have hit : ∀ i < cnt, ∀ S', Inv i S' → Reach Q d f 8 S' (Inv (i + 1)) := by
    rintro i hi S' ⟨hpc', hF, h20, h21, h2⟩
    have h17' : S'.cfg.ptrs 17 = cnt := (hF.ptrs 17 (by decide)).trans h17
    have h1' : S'.cfg.regs 1 = T := (hF.regs 1 (by decide)).trans h1
    have hm : S'.cfg.mem (OW + i) = vals i := by rw [hF.mem]; exact hval i hi
    have hi1 : ¬ cnt ≤ i := by omega
    have hi2 : ¬ (cnt : ℤ) ≤ i := by omega
    have ho' := hF.out
    simp only [Inv]
    rw [sum_range_succ]
    generalize ∑ j ∈ range i, max (vals j - T) 0 = A at h2 ⊢
    by_cases hc : vals i ≤ T
    · apply reach_mono (show 7 ≤ 8 by norm_num) (fun _ h => h)
      apply reach_exact 7
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      simp (config := {contextual := true}) [step, ho', hpc', q3, q4, q5, q6, q8, q9, q10, RAMStep,
        List.getElem?_map, Instr.coreOf, State.next, h17', h20, h21, h2, hm, hc, hi1, hi2, h1',
        fr_iff hF]
      ring
    · apply reach_exact 8
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      simp (config := {contextual := true}) [step, ho', hpc', q3, q4, q5, q6, q7, q8, q9, q10, RAMStep,
        List.getElem?_map, Instr.coreOf, State.next, h17', h20, h21, h2, hm, hc, hi1, hi2, h1',
        fr_iff hF]
      exact ⟨by ring, le_of_lt (lt_of_not_ge hc)⟩
  have hex : ∀ S', Inv cnt S' → Reach Q d f 1 S' (fun S' => S'.cfg.pc = b + 11 ∧
      Fr S S' [20, 21] [2, 5, 6] ∧ S'.cfg.regs 2 = ∑ j ∈ range cnt, max (vals j - T) 0) := by
    rintro S' ⟨hpc', hF, h20, h21, h2⟩
    have h17' : S'.cfg.ptrs 17 = cnt := (hF.ptrs 17 (by decide)).trans h17
    have ho' := hF.out
    apply reach_exact 1
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp [step, ho', hpc', q3, RAMStep, List.getElem?_map, Instr.coreOf, h17', h20, fr_iff hF]
    exact h2
  have := reach_bind h0 (reach_loop_exit cnt hit hex)
  exact reach_mono (by omega) (fun _ h => h) this

theorem hinit_run (b : ℕ) (hE : Emb Q b hinitCode) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) :
    Reach Q d f 2 S (fun S' => S'.cfg.pc = b + 2 ∧ Fr S S' [14] [3] ∧ S'.cfg.regs 3 = 0 ∧
      S'.cfg.ptrs 14 = 0) := by
  have q0 : Q[b]? = some (.core (.const 3 ((0 : ℚ) : ℝ))) := emb_at0 hE (by simp [hinitCode])
  have q1 : Q[b + 1]? = some (.core (.pset 14 0)) := hE 1 (by simp [hinitCode])
  apply reach_exact 2
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q0, q1, RAMStep, List.getElem?_map,
    Instr.coreOf, State.next, fr_iff (Fr.refl ho [14] [3])]

/-- Post-condition of the coin loop. -/
structure CoinPost (S S' : State) (v : ℕ) (c : ℕ) : Prop where
  out : S'.output = none
  ptrs : ∀ j, j ∉ [25, 26] → S'.cfg.ptrs j = S.cfg.ptrs j
  regs : ∀ j, j ≠ 5 → S'.cfg.regs j = S.cfg.regs j
  mem : S'.cfg.mem = S.cfg.mem
  imem : S'.imem = S.imem
  queries : S'.queries = S.queries
  coins : S'.coins = S.coins + c
  p25 : S'.cfg.ptrs 25 = v

lemma coin_iff {S S' : State} (hm : S'.cfg.mem = S.cfg.mem) (hi : S'.imem = S.imem)
    (hq : S'.queries = S.queries) (hp : ∀ j, j ∉ [25, 26] → S'.cfg.ptrs j = S.cfg.ptrs j)
    (hr : ∀ j, j ≠ 5 → S'.cfg.regs j = S.cfg.regs j) (pc : ℕ) (regs : ℕ → ℝ) (ptrs : ℕ → ℤ)
    (c w v k : ℕ) :
    CoinPost S ⟨⟨pc, regs, ptrs, S'.cfg.mem⟩, S'.imem, c, w, S'.queries, none⟩ v k ↔
      ((∀ j, j ∉ [25, 26] → ptrs j = S'.cfg.ptrs j) ∧ (∀ j, j ≠ 5 → regs j = S'.cfg.regs j) ∧
        c = S.coins + k ∧ ptrs 25 = v) := by
  constructor
  · intro h
    exact ⟨fun j hj => (h.ptrs j hj).trans (hp j hj).symm, fun j hj => (h.regs j hj).trans (hr j hj).symm,
      h.coins, h.p25⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨rfl, fun j hj => (h1 j hj).trans (hp j hj), fun j hj => (h2 j hj).trans (hr j hj), hm, hi,
      hq, h3, h4⟩

theorem coin_run (b : ℕ) (hE : Emb Q b (coinCode b)) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (m : ℕ) (h6 : S.cfg.ptrs 6 = m) :
    Reach Q d f (m * 7 + 3) S (fun S' => S'.cfg.pc = b + 9 ∧ CoinPost S S' (dpart f S.coins m) m) := by
  have q0 : Q[b]? = some (.core (.pset 25 0)) := emb_at0 hE (by simp [coinCode])
  have q1 : Q[b + 1]? = some (.core (.pset 26 0)) := hE 1 (by simp [coinCode])
  have q2 : Q[b + 2]? = some (.core (.pjle 6 26 (b + 9))) := hE 2 (by simp [coinCode])
  have q3 : Q[b + 3]? = some (.coin 5) := hE 3 (by simp [coinCode])
  have q4 : Q[b + 4]? = some (.pointerAdd 25 25 25) := hE 4 (by simp [coinCode])
  have q5 : Q[b + 5]? = some (.core (.jle 5 (b + 7))) := hE 5 (by simp [coinCode])
  have q6 : Q[b + 6]? = some (.core (.pinc 25)) := hE 6 (by simp [coinCode])
  have q7 : Q[b + 7]? = some (.core (.pinc 26)) := hE 7 (by simp [coinCode])
  have q8 : Q[b + 8]? = some (.core (.pjle 0 0 (b + 2))) := hE 8 (by simp [coinCode])
  let Inv : ℕ → State → Prop := fun i S' =>
    S'.cfg.pc = b + 2 ∧ CoinPost S S' (dpart f S.coins i) i ∧ S'.cfg.ptrs 26 = i
  have h0 : Reach Q d f 2 S (Inv 0) := by
    apply reach_exact 2
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp (config := {contextual := true}) [step, ho, hpc, q0, q1, RAMStep, List.getElem?_map,
      Instr.coreOf, Inv, State.next, dpart_zero,
      coin_iff (S := S) (S' := S) rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)]
  have hit : ∀ i < m, ∀ S', Inv i S' → Reach Q d f 7 S' (Inv (i + 1)) := by
    rintro i hi S' ⟨hpc', hP, h26⟩
    have h6' : S'.cfg.ptrs 6 = m := (hP.ptrs 6 (by decide)).trans h6
    have hi1 : ¬ m ≤ i := by omega
    have hi2 : ¬ (m : ℤ) ≤ i := by omega
    have ho' := hP.out
    have h25 := hP.p25
    have hc := hP.coins
    have hci := coin_iff hP.mem hP.imem hP.queries hP.ptrs hP.regs
    by_cases hb : f (S.coins + i) = true
    · apply reach_exact 7
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      simp (config := {contextual := true}) [step, ho', hpc', q2, q3, q4, q5, q6, q7, q8, RAMStep,
        List.getElem?_map, Instr.coreOf, State.next, h6', h26, h25, hi1, hi2, hc, hb, show ¬ (1:ℝ) ≤ 0 by norm_num, Inv,
        dpart_succ, hci]
      exact ⟨by ring, by ring⟩
    · apply reach_mono (show 6 ≤ 7 by norm_num) (fun _ h => h)
      apply reach_exact 6
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      simp (config := {contextual := true}) [step, ho', hpc', q2, q3, q4, q5, q6, q7, q8, RAMStep,
        List.getElem?_map, Instr.coreOf, State.next, h6', h26, h25, hi1, hi2, hc, hb, show ¬ (1:ℝ) ≤ 0 by norm_num, Inv,
        dpart_succ, hci]
      exact ⟨by ring, by ring⟩
  have hex : ∀ S', Inv m S' → Reach Q d f 1 S' (fun S' => S'.cfg.pc = b + 9 ∧
      CoinPost S S' (dpart f S.coins m) m) := by
    rintro S' ⟨hpc', hP, h26⟩
    have h6' : S'.cfg.ptrs 6 = m := (hP.ptrs 6 (by decide)).trans h6
    have ho' := hP.out
    apply reach_exact 1
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp [step, ho', hpc', q2, RAMStep, List.getElem?_map, Instr.coreOf, h6', h26]
    exact ⟨rfl, hP.ptrs, hP.regs, hP.mem, hP.imem, hP.queries, hP.coins, hP.p25⟩
  have := reach_bind h0 (reach_loop_exit m hit hex)
  exact reach_mono (by omega) (fun _ h => h) this

theorem test_skip (skip b : ℕ) (hE : Emb Q b (testCode skip)) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (u : ℕ) (h1 : S.cfg.ptrs 1 = n) (h25 : S.cfg.ptrs 25 = u) (hu : n ≤ u) :
    Reach Q d f 1 S (fun S' => S'.cfg.pc = skip ∧ Fr S S' [] []) := by
  have q0 : Q[b]? = some (.core (.pjle 1 25 skip)) := emb_at0 hE (by simp [testCode])
  apply reach_exact 1
  have hu' : (n : ℤ) ≤ u := by exact_mod_cast hu
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp [step, ho, hpc, q0, RAMStep, List.getElem?_map, Instr.coreOf, h1, h25, hu',
    fr_iff (Fr.refl ho [] [])]

theorem test_go (skip b : ℕ) (hE : Emb Q b (testCode skip)) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (u : ℕ) (h1 : S.cfg.ptrs 1 = n) (h25 : S.cfg.ptrs 25 = u) (hu : u < n) :
    Reach Q d f 3 S (fun S' => S'.cfg.pc = b + 3 ∧ Fr S S' [23, 24] [] ∧
      S'.cfg.ptrs 24 = S.cfg.ptrs 4 ∧ S'.cfg.ptrs 23 = S.cfg.ptrs 12) := by
  have q0 : Q[b]? = some (.core (.pjle 1 25 skip)) := emb_at0 hE (by simp [testCode])
  have q1 : Q[b + 1]? = some (.core (.pcopy 24 4)) := hE 1 (by simp [testCode])
  have q2 : Q[b + 2]? = some (.core (.pcopy 23 12)) := hE 2 (by simp [testCode])
  apply reach_exact 3
  have hu' : ¬ (n : ℤ) ≤ u := by omega
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q0, q1, q2, RAMStep, List.getElem?_map,
    Instr.coreOf, State.next, h1, h25, hu', fr_iff (Fr.refl ho [23, 24] [])]

theorem cap_run (b : ℕ) (hE : Emb Q b (capCode b)) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (j : ℕ) (pm T : ℝ) (h1 : S.cfg.ptrs 1 = n) (h20 : S.cfg.ptrs 20 = j)
    (h11 : S.cfg.regs 11 = pm) (hT : S.cfg.regs 1 = T) (h0 : S.cfg.regs 0 = 0) :
    Reach Q d f 5 S (fun S' => S'.cfg.pc = b + 6 ∧ Fr S S' [] [14, 15] ∧
      S'.cfg.regs 15 = if j < n then min pm T else T) := by
  have q0 : Q[b]? = some (.core (.pjle 1 20 (b + 3))) := emb_at0 hE (by simp [capCode])
  have q1 : Q[b + 1]? = some (.core (.sub 14 11 1)) := hE 1 (by simp [capCode])
  have q2 : Q[b + 2]? = some (.core (.jle 14 (b + 5))) := hE 2 (by simp [capCode])
  have q3 : Q[b + 3]? = some (.core (.add 15 1 0)) := hE 3 (by simp [capCode])
  have q4 : Q[b + 4]? = some (.core (.pjle 0 0 (b + 6))) := hE 4 (by simp [capCode])
  have q5 : Q[b + 5]? = some (.core (.add 15 11 0)) := hE 5 (by simp [capCode])
  by_cases hj : j < n
  · have hj' : ¬ (n : ℤ) ≤ j := by omega
    by_cases hc : pm ≤ T
    · apply reach_mono (show 4 ≤ 5 by norm_num) (fun _ h => h)
      apply reach_exact 4
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      simp (config := {contextual := true}) [step, ho, hpc, q0, q1, q2, q5, RAMStep,
        List.getElem?_map, Instr.coreOf, State.next, h1, h20, hj, hj', h11, hT, h0, hc,
        fr_iff (Fr.refl ho [] [14, 15])]
    · apply reach_exact 5
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      simp (config := {contextual := true}) [step, ho, hpc, q0, q1, q2, q3, q4, RAMStep,
        List.getElem?_map, Instr.coreOf, State.next, h1, h20, hj, hj', h11, hT, h0, hc,
        fr_iff (Fr.refl ho [] [14, 15])]
      all_goals (try simp only [max_def])
      all_goals (try split_ifs)
      all_goals first | ring1 | (exfalso; linarith [lt_of_not_ge hc]) | linarith [lt_of_not_ge hc]
  · have hj' : (n : ℤ) ≤ j := by omega
    apply reach_mono (show 3 ≤ 5 by norm_num) (fun _ h => h)
    apply reach_exact 3
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp (config := {contextual := true}) [step, ho, hpc, q0, q3, q4, RAMStep,
      List.getElem?_map, Instr.coreOf, State.next, h1, h20, hj, hj', hT, h0,
      fr_iff (Fr.refl ho [] [14, 15])]

end MTSPEst

end

section

/-! Verification of the per-sample loop, the outer-loop head/tail and the output code. -/

open scoped Classical

namespace MTSPEst
open SublinearSteiner SmaleNinth Finset

variable {Q : Program} {n : ℕ} {d : Fin n → Fin n → ℝ} {f : ℕ → Bool}

/-- Partial sums of `MTSPMst.hcap`. -/
noncomputable def hpart (n : ℕ) (T : ℝ) (vals : List ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ range i, (1 / ((j : ℝ) + 1)) * (MTSPMst.capF n T vals (j + 1) - MTSPMst.capF n T vals j)

section hloop
variable (b : ℕ) (hE : Emb Q b (hloopCode b))
include hE

theorem hl_init (S : State) (hpc : S.cfg.pc = b) (ho : S.output = none) (OW : ℤ)
    (h10 : S.cfg.ptrs 10 = OW) :
    Reach Q d f 4 S (fun S' => S'.cfg.pc = b + 4 ∧ Fr S S' [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19] ∧
      S'.cfg.ptrs 20 = 0 ∧ S'.cfg.ptrs 21 = OW ∧ S'.cfg.regs 11 = 0 ∧ S'.cfg.regs 10 = 0) := by
  have q0 : Q[b]? = some (.core (.const 10 ((0 : ℚ) : ℝ))) := emb_at0 hE (by simp [hloopCode, hA])
  have q1 : Q[b + 1]? = some (.core (.const 11 ((0 : ℚ) : ℝ))) := hE 1 (by simp [hloopCode, hA])
  have q2 : Q[b + 2]? = some (.core (.pset 20 0)) := hE 2 (by simp [hloopCode, hA])
  have q3 : Q[b + 3]? = some (.core (.pcopy 21 10)) := hE 3 (by simp [hloopCode, hA])
  apply reach_exact 4
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q0, q1, q2, q3, RAMStep,
    List.getElem?_map, Instr.coreOf, State.next, h10, fr_iff (Fr.refl ho [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19])]

theorem hl_add (S0 S : State) (hpc : S.cfg.pc = b + 10) (hF : Fr S0 S [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19]) (h0 : S.cfg.regs 0 = 0) :
    Reach Q d f 1 S (fun S' => S'.cfg.pc = b + 11 ∧ Fr S0 S' [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19] ∧
      S'.cfg.regs 12 = S.cfg.regs 15 ∧ S'.cfg.ptrs = S.cfg.ptrs ∧
      ∀ j, j ≠ 12 → S'.cfg.regs j = S.cfg.regs j) := by
  have q10 : Q[b + 10]? = some (.core (.add 12 15 0)) := hE 10 (by simp [hloopCode, hA, hB, capCode])
  have ho := hF.out
  apply reach_exact 1
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q10, RAMStep, List.getElem?_map,
    Instr.coreOf, State.next, h0, fr_iff hF, Function.update_apply]

theorem hl_p1a (S0 S : State) (hpc : S.cfg.pc = b + 11) (hF : Fr S0 S [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19]) (i s cnt : ℕ) (OW : ℤ)
    (pm v : ℝ) (h4 : S.cfg.ptrs 4 = s) (h18 : S.cfg.ptrs 18 = cnt) (h20 : S.cfg.ptrs 20 = i)
    (h21 : S.cfg.ptrs 21 = OW + i) (h11 : S.cfg.regs 11 = pm) (hm : S.cfg.mem (OW + i) = v)
    (hi : i < s) (hc : i < cnt) (hv : v ≤ pm) :
    Reach Q d f 7 S (fun S' => S'.cfg.pc = b + 19 ∧ Fr S0 S' [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19] ∧ S'.cfg.ptrs 20 = (i + 1 : ℕ) ∧
      S'.cfg.ptrs 21 = OW + (i + 1 : ℕ) ∧ S'.cfg.regs 11 = pm ∧ S'.cfg.regs 12 = S.cfg.regs 12 ∧
      S'.cfg.regs 10 = S.cfg.regs 10) := by
  have q11 : Q[b + 11]? = some (.core (.pjle 4 20 (b + 31))) := hE 11 (by simp [hloopCode, hA, hB, capCode])
  have q12 : Q[b + 12]? = some (.core (.pjle 18 20 (b + 17))) := hE 12 (by simp [hloopCode, hA, hB, capCode])
  have q13 : Q[b + 13]? = some (.core (.load 16 21)) := hE 13 (by simp [hloopCode, hA, hB, capCode])
  have q14 : Q[b + 14]? = some (.core (.sub 17 16 11)) := hE 14 (by simp [hloopCode, hA, hB, capCode])
  have q15 : Q[b + 15]? = some (.core (.jle 17 (b + 17))) := hE 15 (by simp [hloopCode, hA, hB, capCode])
  have q17 : Q[b + 17]? = some (.core (.pinc 20)) := hE 17 (by simp [hloopCode, hA, hB, capCode])
  have q18 : Q[b + 18]? = some (.core (.pinc 21)) := hE 18 (by simp [hloopCode, hA, hB, capCode])
  have ho := hF.out
  have hi2 : ¬ (s : ℤ) ≤ i := by omega
  have hc2 : ¬ (cnt : ℤ) ≤ i := by omega
  apply reach_exact 7
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q11, q12, q13, q14, q15, q17, q18, RAMStep,
    List.getElem?_map, Instr.coreOf, State.next, h4, h18, h20, h21, h11, hm, hi2, hc2, hv, fr_iff hF]
  ring

theorem hl_p1b (S0 S : State) (hpc : S.cfg.pc = b + 11) (hF : Fr S0 S [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19]) (i s cnt : ℕ) (OW : ℤ)
    (pm v : ℝ) (h4 : S.cfg.ptrs 4 = s) (h18 : S.cfg.ptrs 18 = cnt) (h20 : S.cfg.ptrs 20 = i)
    (h21 : S.cfg.ptrs 21 = OW + i) (h11 : S.cfg.regs 11 = pm) (hm : S.cfg.mem (OW + i) = v)
    (hi : i < s) (hc : i < cnt) (hv : ¬ v ≤ pm) :
    Reach Q d f 8 S (fun S' => S'.cfg.pc = b + 19 ∧ Fr S0 S' [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19] ∧ S'.cfg.ptrs 20 = (i + 1 : ℕ) ∧
      S'.cfg.ptrs 21 = OW + (i + 1 : ℕ) ∧ S'.cfg.regs 11 = v ∧ S'.cfg.regs 12 = S.cfg.regs 12 ∧
      S'.cfg.regs 10 = S.cfg.regs 10) := by
  have q11 : Q[b + 11]? = some (.core (.pjle 4 20 (b + 31))) := hE 11 (by simp [hloopCode, hA, hB, capCode])
  have q12 : Q[b + 12]? = some (.core (.pjle 18 20 (b + 17))) := hE 12 (by simp [hloopCode, hA, hB, capCode])
  have q13 : Q[b + 13]? = some (.core (.load 16 21)) := hE 13 (by simp [hloopCode, hA, hB, capCode])
  have q14 : Q[b + 14]? = some (.core (.sub 17 16 11)) := hE 14 (by simp [hloopCode, hA, hB, capCode])
  have q15 : Q[b + 15]? = some (.core (.jle 17 (b + 17))) := hE 15 (by simp [hloopCode, hA, hB, capCode])
  have q16 : Q[b + 16]? = some (.core (.add 11 11 17)) := hE 16 (by simp [hloopCode, hA, hB, capCode])
  have q17 : Q[b + 17]? = some (.core (.pinc 20)) := hE 17 (by simp [hloopCode, hA, hB, capCode])
  have q18 : Q[b + 18]? = some (.core (.pinc 21)) := hE 18 (by simp [hloopCode, hA, hB, capCode])
  have ho := hF.out
  have hi2 : ¬ (s : ℤ) ≤ i := by omega
  have hc2 : ¬ (cnt : ℤ) ≤ i := by omega
  apply reach_exact 8
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q11, q12, q13, q14, q15, q16, q17, q18,
    RAMStep, List.getElem?_map, Instr.coreOf, State.next, h4, h18, h20, h21, h11, hm, hi2, hc2, hv,
    fr_iff hF]
  ring

theorem hl_p1c (S0 S : State) (hpc : S.cfg.pc = b + 11) (hF : Fr S0 S [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19]) (i s cnt : ℕ) (OW : ℤ)
    (h4 : S.cfg.ptrs 4 = s) (h18 : S.cfg.ptrs 18 = cnt) (h20 : S.cfg.ptrs 20 = i)
    (h21 : S.cfg.ptrs 21 = OW + i) (hi : i < s) (hc : cnt ≤ i) :
    Reach Q d f 4 S (fun S' => S'.cfg.pc = b + 19 ∧ Fr S0 S' [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19] ∧ S'.cfg.ptrs 20 = (i + 1 : ℕ) ∧
      S'.cfg.ptrs 21 = OW + (i + 1 : ℕ) ∧ S'.cfg.regs 11 = S.cfg.regs 11 ∧
      S'.cfg.regs 12 = S.cfg.regs 12 ∧ S'.cfg.regs 10 = S.cfg.regs 10) := by
  have q11 : Q[b + 11]? = some (.core (.pjle 4 20 (b + 31))) := hE 11 (by simp [hloopCode, hA, hB, capCode])
  have q12 : Q[b + 12]? = some (.core (.pjle 18 20 (b + 17))) := hE 12 (by simp [hloopCode, hA, hB, capCode])
  have q17 : Q[b + 17]? = some (.core (.pinc 20)) := hE 17 (by simp [hloopCode, hA, hB, capCode])
  have q18 : Q[b + 18]? = some (.core (.pinc 21)) := hE 18 (by simp [hloopCode, hA, hB, capCode])
  have ho := hF.out
  have hi2 : ¬ (s : ℤ) ≤ i := by omega
  have hc2 : (cnt : ℤ) ≤ i := by omega
  apply reach_exact 4
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q11, q12, q17, q18, RAMStep,
    List.getElem?_map, Instr.coreOf, State.next, h4, h18, h20, h21, hi2, hc2, fr_iff hF]
  ring

theorem hl_p3 (S0 S : State) (hpc : S.cfg.pc = b + 25) (hF : Fr S0 S [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19]) (i : ℕ) (c c' H : ℝ)
    (h15 : S.cfg.regs 15 = c') (h12 : S.cfg.regs 12 = c) (h10 : S.cfg.regs 10 = H)
    (h20 : S.cfg.ptrs 20 = (i + 1 : ℕ)) :
    Reach Q d f 6 S (fun S' => S'.cfg.pc = b + 11 ∧ Fr S0 S' [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19] ∧ S'.cfg.regs 12 = c' ∧
      S'.cfg.regs 10 = H + (c' - c) / ((i : ℝ) + 1) ∧ S'.cfg.ptrs = S.cfg.ptrs ∧
      S'.cfg.regs 11 = S.cfg.regs 11) := by
  have q25 : Q[b + 25]? = some (.core (.sub 18 15 12)) := hE 25 (by simp [hloopCode, hA, hB, hC, capCode])
  have q26 : Q[b + 26]? = some (.core (.add 12 12 18)) := hE 26 (by simp [hloopCode, hA, hB, hC, capCode])
  have q27 : Q[b + 27]? = some (.pointerReal 19 20) := hE 27 (by simp [hloopCode, hA, hB, hC, capCode])
  have q28 : Q[b + 28]? = some (.core (.div 18 18 19)) := hE 28 (by simp [hloopCode, hA, hB, hC, capCode])
  have q29 : Q[b + 29]? = some (.core (.add 10 10 18)) := hE 29 (by simp [hloopCode, hA, hB, hC, capCode])
  have q30 : Q[b + 30]? = some (.core (.pjle 0 0 (b + 11))) := hE 30 (by simp [hloopCode, hA, hB, hC, capCode])
  have ho := hF.out
  apply reach_exact 6
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q25, q26, q27, q28, q29, q30, RAMStep,
    List.getElem?_map, Instr.coreOf, State.next, h15, h12, h10, h20, fr_iff hF]

theorem hl_exit (S0 S : State) (hpc : S.cfg.pc = b + 11) (hF : Fr S0 S [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19]) (s : ℕ)
    (h4 : S.cfg.ptrs 4 = s) (h20 : S.cfg.ptrs 20 = s) :
    Reach Q d f 1 S (fun S' => S'.cfg.pc = b + 31 ∧ Fr S0 S' [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19] ∧ S'.cfg.regs = S.cfg.regs) := by
  have q11 : Q[b + 11]? = some (.core (.pjle 4 20 (b + 31))) := hE 11 (by simp [hloopCode, hA, hB, capCode])
  have ho := hF.out
  apply reach_exact 1
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp [step, ho, hpc, q11, RAMStep, List.getElem?_map, Instr.coreOf, h4, h20, fr_iff hF]

end hloop

theorem hloop_run (b : ℕ) (hE : Emb Q b (hloopCode b)) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (s cnt : ℕ) (OW : ℤ) (T : ℝ) (vals : List ℝ)
    (h1 : S.cfg.ptrs 1 = n) (h4 : S.cfg.ptrs 4 = s) (h18 : S.cfg.ptrs 18 = cnt)
    (h10 : S.cfg.ptrs 10 = OW) (hT : S.cfg.regs 1 = T) (h0 : S.cfg.regs 0 = 0)
    (hcnt : cnt = vals.length) (hval : ∀ j, j < cnt → S.cfg.mem (OW + j) = vals.getD j 0) :
    Reach Q d f (s * 19 + 12) S (fun S' => S'.cfg.pc = b + 31 ∧ Fr S S' [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19] ∧
      S'.cfg.regs 10 = MTSPMst.hcap n s T vals) := by
  obtain ⟨-, hE'⟩ := emb_split hE (show b + hA.length = b + 4 from rfl)
  obtain ⟨eC1, hE'⟩ := emb_split hE' (show b + 4 + (capCode (b + 4)).length = b + 10 from rfl)
  obtain ⟨-, hE'⟩ := emb_split hE' (show b + 10 + (hB b).length = b + 19 from rfl)
  obtain ⟨eC2, -⟩ := emb_split hE' (show b + 19 + (capCode (b + 19)).length = b + 25 from rfl)
  let Inv : ℕ → State → Prop := fun i S' =>
    S'.cfg.pc = b + 11 ∧ Fr S S' [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19] ∧ S'.cfg.ptrs 20 = i ∧ S'.cfg.ptrs 21 = OW + i ∧
      S'.cfg.regs 11 = MTSPMst.pmax vals i ∧ S'.cfg.regs 12 = MTSPMst.capF n T vals i ∧
      S'.cfg.regs 10 = hpart n T vals i
  have hI0 : Reach Q d f (4 + (5 + 1)) S (Inv 0) := by
    refine reach_bind (hl_init b hE S hpc ho OW h10) ?_
    rintro S1 ⟨hpc1, hF1, h20, h21, h11, h10'⟩
    refine reach_bind (cap_run (b + 4) eC1 S1 hpc1 hF1.out 0 0 T
      ((hF1.ptrs 1 (by decide)).trans h1) h20 h11 ((hF1.regs 1 (by decide)).trans hT)
      ((hF1.regs 0 (by decide)).trans h0)) ?_
    rintro S2 ⟨hpc2, hF2, h15⟩
    have hF2' : Fr S S2 [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19] := (hF1.trans hF2).mono (by decide) (by decide)
    refine reach_mono le_rfl ?_ (hl_add b hE S S2 hpc2 hF2' ((hF2'.regs 0 (by decide)).trans h0))
    rintro S3 ⟨hpc3, hF3, h12, hp3, hr3⟩
    refine ⟨hpc3, hF3, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hp3, hF2.ptrs 20 (by decide), h20]; rfl
    · rw [hp3, hF2.ptrs 21 (by decide), h21]; simp
    · rw [hr3 11 (by decide), hF2.regs 11 (by decide), h11, pmax_zero]
    · rw [h12, h15]; simp [MTSPMst.capF, pmax_zero]
    · rw [hr3 10 (by decide), hF2.regs 10 (by decide), h10']; simp [hpart]
  have hit : ∀ i < s, ∀ S', Inv i S' → Reach Q d f (8 + (5 + 6)) S' (Inv (i + 1)) := by
    rintro i hi S' ⟨hpc', hF, h20, h21, h11, h12, h10'⟩
    have h4' : S'.cfg.ptrs 4 = s := (hF.ptrs 4 (by decide)).trans h4
    have h18' : S'.cfg.ptrs 18 = cnt := (hF.ptrs 18 (by decide)).trans h18
    have P1 : Reach Q d f 8 S' (fun S2 => S2.cfg.pc = b + 19 ∧ Fr S S2 [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19] ∧
        S2.cfg.ptrs 20 = (i + 1 : ℕ) ∧ S2.cfg.ptrs 21 = OW + (i + 1 : ℕ) ∧
        S2.cfg.regs 11 = MTSPMst.pmax vals (i + 1) ∧ S2.cfg.regs 12 = MTSPMst.capF n T vals i ∧
        S2.cfg.regs 10 = hpart n T vals i) := by
      rw [pmax_succ]
      by_cases hc : i < cnt
      · have hm : S'.cfg.mem (OW + i) = vals.getD i 0 := by rw [hF.mem]; exact hval i hc
        have hlen : i < vals.length := by omega
        simp only [hlen, if_true]
        by_cases hv : vals.getD i 0 ≤ MTSPMst.pmax vals i
        · refine reach_mono (by norm_num) ?_ (hl_p1a b hE S S' hpc' hF i s cnt OW _ _ h4' h18' h20
            h21 h11 hm hi hc hv)
          rintro S2 ⟨a1, a2, a3, a4, a5, a6, a7⟩
          exact ⟨a1, a2, a3, a4, by rw [a5, max_eq_left hv], a6.trans h12, a7.trans h10'⟩
        · refine reach_mono le_rfl ?_ (hl_p1b b hE S S' hpc' hF i s cnt OW _ _ h4' h18' h20
            h21 h11 hm hi hc hv)
          rintro S2 ⟨a1, a2, a3, a4, a5, a6, a7⟩
          exact ⟨a1, a2, a3, a4, by rw [a5, max_eq_right (le_of_lt (lt_of_not_ge hv))],
            a6.trans h12, a7.trans h10'⟩
      · have hlen : ¬ i < vals.length := by omega
        simp only [hlen, if_false]
        refine reach_mono (by norm_num) ?_ (hl_p1c b hE S S' hpc' hF i s cnt OW h4' h18' h20 h21
          hi (by omega))
        rintro S2 ⟨a1, a2, a3, a4, a5, a6, a7⟩
        exact ⟨a1, a2, a3, a4, a5.trans h11, a6.trans h12, a7.trans h10'⟩
    refine reach_bind P1 ?_
    rintro S2 ⟨hpc2, hF2, h20', h21', h11', h12', h10''⟩
    refine reach_bind (cap_run (b + 19) eC2 S2 hpc2 hF2.out (i + 1) _ T
      ((hF2.ptrs 1 (by decide)).trans h1) h20' h11' ((hF2.regs 1 (by decide)).trans hT)
      ((hF2.regs 0 (by decide)).trans h0)) ?_
    rintro S3 ⟨hpc3, hF3, h15⟩
    have hF3' : Fr S S3 [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19] := (hF2.trans hF3).mono (by decide) (by decide)
    refine reach_mono le_rfl ?_ (hl_p3 b hE S S3 hpc3 hF3' i _ _ _ h15
      ((hF3.regs 12 (by decide)).trans h12') ((hF3.regs 10 (by decide)).trans h10'')
      ((hF3.ptrs 20 (by decide)).trans h20'))
    rintro S4 ⟨a1, a2, a3, a4, a5, a6⟩
    refine ⟨a1, a2, ?_, ?_, ?_, a3, ?_⟩
    · rw [a5, hF3.ptrs 20 (by decide), h20']
    · rw [a5, hF3.ptrs 21 (by decide), h21']
    · rw [a6, hF3.regs 11 (by decide), h11']
    · rw [a4]; unfold hpart; rw [sum_range_succ]; simp only [MTSPMst.capF]; push_cast; ring
  have hex : ∀ S', Inv s S' → Reach Q d f 1 S' (fun S' => S'.cfg.pc = b + 31 ∧
      Fr S S' [20, 21] [10, 11, 12, 14, 15, 16, 17, 18, 19] ∧ S'.cfg.regs 10 = MTSPMst.hcap n s T vals) := by
    rintro S' ⟨hpc', hF, h20, h21, h11, h12, h10'⟩
    refine reach_mono le_rfl ?_ (hl_exit b hE S S' hpc' hF s ((hF.ptrs 4 (by decide)).trans h4) h20)
    rintro S2 ⟨a1, a2, a3⟩
    exact ⟨a1, a2, by rw [a3, h10']; unfold hpart MTSPMst.hcap; rfl⟩
  have := reach_bind hI0 (reach_loop_exit s hit hex)
  exact reach_mono (by omega) (fun _ h => h) this

theorem tail_run (oh b : ℕ) (hE : Emb Q b (tailCode oh)) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) :
    Reach Q d f 3 S (fun S' => S'.cfg.pc = oh ∧ Fr S S' [14] [3] ∧
      S'.cfg.regs 3 = S.cfg.regs 3 + S.cfg.regs 10 ∧ S'.cfg.ptrs 14 = S.cfg.ptrs 14 + 1) := by
  have q0 : Q[b]? = some (.core (.add 3 3 10)) := emb_at0 hE (by simp [tailCode])
  have q1 : Q[b + 1]? = some (.core (.pinc 14)) := hE 1 (by simp [tailCode])
  have q2 : Q[b + 2]? = some (.core (.pjle 0 0 oh)) := hE 2 (by simp [tailCode])
  apply reach_exact 3
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q0, q1, q2, RAMStep, List.getElem?_map,
    Instr.coreOf, State.next, fr_iff (Fr.refl ho [14] [3])]

theorem tail_skip (oh b : ℕ) (hE : Emb Q b (tailCode oh)) (S : State) (hpc : S.cfg.pc = b + 1)
    (ho : S.output = none) :
    Reach Q d f 2 S (fun S' => S'.cfg.pc = oh ∧ Fr S S' [14] [] ∧
      S'.cfg.ptrs 14 = S.cfg.ptrs 14 + 1) := by
  have q1 : Q[b + 1]? = some (.core (.pinc 14)) := hE 1 (by simp [tailCode])
  have q2 : Q[b + 2]? = some (.core (.pjle 0 0 oh)) := hE 2 (by simp [tailCode])
  apply reach_exact 2
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q1, q2, RAMStep, List.getElem?_map,
    Instr.coreOf, State.next, fr_iff (Fr.refl ho [14] [])]

theorem head_go (ex b : ℕ) (hE : Emb Q b [.core (.pjle 5 14 ex)]) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (r i : ℕ) (h5 : S.cfg.ptrs 5 = r) (h14 : S.cfg.ptrs 14 = i) (hi : i < r) :
    Reach Q d f 1 S (fun S' => S'.cfg.pc = b + 1 ∧ Fr S S' [] []) := by
  have q0 : Q[b]? = some (.core (.pjle 5 14 ex)) := emb_at0 hE (by simp)
  apply reach_exact 1
  have hi' : ¬ (r : ℤ) ≤ i := by omega
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp [step, ho, hpc, q0, RAMStep, List.getElem?_map, Instr.coreOf, h5, h14, hi',
    fr_iff (Fr.refl ho [] [])]

theorem head_exit (ex b : ℕ) (hE : Emb Q b [.core (.pjle 5 14 ex)]) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (r : ℕ) (h5 : S.cfg.ptrs 5 = r) (h14 : S.cfg.ptrs 14 = r) :
    Reach Q d f 1 S (fun S' => S'.cfg.pc = ex ∧ Fr S S' [] []) := by
  have q0 : Q[b]? = some (.core (.pjle 5 14 ex)) := emb_at0 hE (by simp)
  apply reach_exact 1
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp [step, ho, hpc, q0, RAMStep, List.getElem?_map, Instr.coreOf, h5, h14,
    fr_iff (Fr.refl ho [] [])]

theorem final_run (scale : ℚ) (b : ℕ) (hE : Emb Q b (finalCode scale)) (S : State)
    (hpc : S.cfg.pc = b) (ho : S.output = none) (m r : ℕ) (h7 : S.cfg.ptrs 7 = 2 ^ m)
    (h5 : S.cfg.ptrs 5 = r) :
    Reach Q d f 9 S (fun S' => S'.output = some ((S.cfg.regs 2 + ((2 : ℝ) ^ m / (r : ℝ)) *
      S.cfg.regs 3 - S.cfg.regs 1) * (scale : ℝ)) ∧ S'.queries = S.queries ∧ S'.coins = S.coins) := by
  have q0 : Q[b]? = some (.pointerReal 20 7) := emb_at0 hE (by simp [finalCode])
  have q1 : Q[b + 1]? = some (.pointerReal 21 5) := hE 1 (by simp [finalCode])
  have q2 : Q[b + 2]? = some (.core (.div 22 20 21)) := hE 2 (by simp [finalCode])
  have q3 : Q[b + 3]? = some (.core (.mul 23 22 3)) := hE 3 (by simp [finalCode])
  have q4 : Q[b + 4]? = some (.core (.add 24 2 23)) := hE 4 (by simp [finalCode])
  have q5 : Q[b + 5]? = some (.core (.sub 25 24 1)) := hE 5 (by simp [finalCode])
  have q6 : Q[b + 6]? = some (.core (.const 26 (scale : ℝ))) := hE 6 (by simp [finalCode])
  have q7 : Q[b + 7]? = some (.core (.mul 27 25 26)) := hE 7 (by simp [finalCode])
  have q8 : Q[b + 8]? = some (.halt 27) := hE 8 (by simp [finalCode])
  apply reach_exact 9
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp [step, ho, hpc, q0, q1, q2, q3, q4, q5, q6, q7, q8, RAMStep, List.getElem?_map,
    Instr.coreOf, State.next, h7, h5]

end MTSPEst

end

section

/-! Verification of the prefix blocks (setup, parameter computation, layout). -/

open scoped Classical

namespace MTSPEst
open SublinearSteiner SmaleNinth

variable {Q : Program} {n : ℕ} {d : Fin n → Fin n → ℝ} {f : ℕ → Bool}

theorem setup_halt (b : ℕ) (hE : Emb Q b (setupCode b)) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (hp0 : S.cfg.ptrs 0 = 0) (hi0 : S.imem 0 = n) (hn : n ≤ 1) :
    Reach Q d f 5 S (fun S' => S'.output = some 0 ∧ S'.queries = S.queries ∧ S'.coins = S.coins) := by
  have q0 : Q[b]? = some (.integerLoad 1 0) := emb_at0 hE (by simp [setupCode])
  have q1 : Q[b + 1]? = some (.core (.pset 12 1)) := hE 1 (by simp [setupCode])
  have q2 : Q[b + 2]? = some (.core (.pjle 1 12 (b + 4))) := hE 2 (by simp [setupCode])
  have q4 : Q[b + 4]? = some (.core (.const 5 ((0 : ℚ) : ℝ))) := hE 4 (by simp [setupCode])
  have q5 : Q[b + 5]? = some (.halt 5) := hE 5 (by simp [setupCode])
  apply reach_exact 5
  have hn' : (n : ℤ) ≤ 1 := by exact_mod_cast hn
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q0, q1, q2, q4, q5, RAMStep, List.getElem?_map, Instr.coreOf,
    State.next, hp0, hi0, hn']

theorem setup_run (b : ℕ) (hE : Emb Q b (setupCode b)) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (hp0 : S.cfg.ptrs 0 = 0) (hi0 : S.imem 0 = n) (hn : ¬ n ≤ 1) :
    Reach Q d f 4 S (fun S' => S'.cfg.pc = b + 6 ∧ Fr S S' [1, 12] [] ∧ S'.cfg.ptrs 1 = n ∧
      S'.cfg.ptrs 12 = 1) := by
  have q0 : Q[b]? = some (.integerLoad 1 0) := emb_at0 hE (by simp [setupCode])
  have q1 : Q[b + 1]? = some (.core (.pset 12 1)) := hE 1 (by simp [setupCode])
  have q2 : Q[b + 2]? = some (.core (.pjle 1 12 (b + 4))) := hE 2 (by simp [setupCode])
  have q3 : Q[b + 3]? = some (.core (.pjle 0 0 (b + 6))) := hE 3 (by simp [setupCode])
  apply reach_exact 4
  have hn' : ¬ (n : ℤ) ≤ 1 := by exact_mod_cast hn
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q0, q1, q2, q3, RAMStep, List.getElem?_map, Instr.coreOf,
    State.next, hp0, hi0, hn', fr_iff (Fr.refl ho [1, 12] [])]

theorem qloop_run (b : ℕ) (hE : Emb Q b (qloopCode b)) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (h1 : S.cfg.ptrs 1 = n) :
    Reach Q d f (qOf n * 8 + 7) S (fun S' => S'.cfg.pc = b + 9 ∧ Fr S S' [2] [5, 6, 7, 8] ∧
      S'.cfg.ptrs 2 = qOf n) := by
  have q0 : Q[b]? = some (.core (.pset 2 1)) := emb_at0 hE (by simp [qloopCode])
  have q1 : Q[b + 1]? = some (.pointerReal 5 2) := hE 1 (by simp [qloopCode])
  have q2 : Q[b + 2]? = some (.core (.mul 6 5 5)) := hE 2 (by simp [qloopCode])
  have q3 : Q[b + 3]? = some (.core (.mul 6 6 6)) := hE 3 (by simp [qloopCode])
  have q4 : Q[b + 4]? = some (.pointerReal 7 1) := hE 4 (by simp [qloopCode])
  have q5 : Q[b + 5]? = some (.core (.sub 8 7 6)) := hE 5 (by simp [qloopCode])
  have q6 : Q[b + 6]? = some (.core (.jle 8 (b + 9))) := hE 6 (by simp [qloopCode])
  have q7 : Q[b + 7]? = some (.core (.pinc 2)) := hE 7 (by simp [qloopCode])
  have q8 : Q[b + 8]? = some (.core (.pjle 0 0 (b + 1))) := hE 8 (by simp [qloopCode])
  let Inv : ℕ → State → Prop := fun i S' =>
    S'.cfg.pc = b + 1 ∧ Fr S S' [2] [5, 6, 7, 8] ∧ S'.cfg.ptrs 2 = (i + 1 : ℕ)
  have h0 : Reach Q d f 1 S (Inv 0) := by
    apply reach_exact 1
    simp only [Function.iterate_one]
    simp (config := {contextual := true}) [step, ho, hpc, q0, RAMStep, List.getElem?_map,
      Instr.coreOf, Inv, fr_iff (Fr.refl ho [2] [5, 6, 7, 8])]
  have hit : ∀ i < qOf n - 1, ∀ S', Inv i S' → Reach Q d f 8 S' (Inv (i + 1)) := by
    rintro i hi S' ⟨hpc', hF, h2⟩
    apply reach_exact 8
    have h1' : S'.cfg.ptrs 1 = n := (hF.ptrs 1 (by decide)).trans h1
    have hlt := qOf_min n (i + 1) (by omega) (by omega)
    have hlt' : ¬ (n : ℝ) ≤ ((i : ℝ) + 1) * ((i : ℝ) + 1) * (((i : ℝ) + 1) * ((i : ℝ) + 1)) := by
      rw [not_le]; exact_mod_cast (by nlinarith [hlt] : (i + 1) * (i + 1) * ((i + 1) * (i + 1)) < n)
    have ho' := hF.out
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp (config := {contextual := true}) [step, ho', hpc', q1, q2, q3, q4, q5, q6, q7, q8, RAMStep,
      List.getElem?_map, Instr.coreOf, State.next, h1', h2, hlt', Inv, fr_iff hF]
  have hex : ∀ S', Inv (qOf n - 1) S' → Reach Q d f 6 S'
      (fun S' => S'.cfg.pc = b + 9 ∧ Fr S S' [2] [5, 6, 7, 8] ∧ S'.cfg.ptrs 2 = qOf n) := by
    rintro S' ⟨hpc', hF, h2⟩
    apply reach_exact 6
    have h1' : S'.cfg.ptrs 1 = n := (hF.ptrs 1 (by decide)).trans h1
    have hq1 := qOf_pos n
    have h2' : S'.cfg.ptrs 2 = qOf n := by rw [h2]; congr 1; omega
    have hge : (n : ℝ) ≤ (qOf n : ℝ) * (qOf n) * ((qOf n) * (qOf n)) := by
      exact_mod_cast (by nlinarith [qOf_spec n] : n ≤ qOf n * qOf n * (qOf n * qOf n))
    have ho' := hF.out
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp (config := {contextual := true}) [step, ho', hpc', q1, q2, q3, q4, q5, q6, RAMStep, List.getElem?_map, Instr.coreOf,
      State.next, h1', h2', hge, fr_iff hF]
  have := reach_bind h0 (reach_loop_exit (qOf n - 1) hit hex)
  refine reach_mono ?_ (fun _ h => h) this
  have := qOf_pos n
  omega

theorem countUp_run (b : ℕ) (hE : Emb Q b (countUpCode b)) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (v : ℕ) (hv : S.cfg.regs 25 = v) :
    Reach Q d f (v * 5 + 4) S
      (fun S' => S'.cfg.pc = b + 6 ∧ Fr S S' [22] [13, 14] ∧ S'.cfg.ptrs 22 = v) := by
  have q0 : Q[b]? = some (.core (.pset 22 0)) := emb_at0 hE (by simp [countUpCode])
  have q1 : Q[b + 1]? = some (.pointerReal 13 22) := hE 1 (by simp [countUpCode])
  have q2 : Q[b + 2]? = some (.core (.sub 14 25 13)) := hE 2 (by simp [countUpCode])
  have q3 : Q[b + 3]? = some (.core (.jle 14 (b + 6))) := hE 3 (by simp [countUpCode])
  have q4 : Q[b + 4]? = some (.core (.pinc 22)) := hE 4 (by simp [countUpCode])
  have q5 : Q[b + 5]? = some (.core (.pjle 0 0 (b + 1))) := hE 5 (by simp [countUpCode])
  let Inv : ℕ → State → Prop := fun i S' =>
    S'.cfg.pc = b + 1 ∧ Fr S S' [22] [13, 14] ∧ S'.cfg.ptrs 22 = i
  have h0 : Reach Q d f 1 S (Inv 0) := by
    apply reach_exact 1
    simp only [Function.iterate_one]
    simp (config := {contextual := true}) [step, ho, hpc, q0, RAMStep, List.getElem?_map,
      Instr.coreOf, Inv, fr_iff (Fr.refl ho [22] [13, 14])]
  have hit : ∀ i < v, ∀ S', Inv i S' → Reach Q d f 5 S' (Inv (i + 1)) := by
    rintro i hi S' ⟨hpc', hF, h22⟩
    apply reach_exact 5
    have h25 : S'.cfg.regs 25 = v := (hF.regs 25 (by decide)).trans hv
    have hlt : ¬ (v : ℝ) ≤ i := by exact_mod_cast (not_le.mpr hi)
    have ho' := hF.out
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp (config := {contextual := true}) [step, ho', hpc', q1, q2, q3, q4, q5, RAMStep, List.getElem?_map, Instr.coreOf,
      State.next, h22, h25, hlt, Inv, fr_iff hF]
  have hex : ∀ S', Inv v S' → Reach Q d f 3 S'
      (fun S' => S'.cfg.pc = b + 6 ∧ Fr S S' [22] [13, 14] ∧ S'.cfg.ptrs 22 = v) := by
    rintro S' ⟨hpc', hF, h22⟩
    apply reach_exact 3
    have h25 : S'.cfg.regs 25 = v := (hF.regs 25 (by decide)).trans hv
    have ho' := hF.out
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp (config := {contextual := true}) [step, ho', hpc', q1, q2, q3, RAMStep, List.getElem?_map, Instr.coreOf,
      State.next, h22, h25, fr_iff hF]
  have := reach_bind h0 (reach_loop_exit v hit hex)
  exact reach_mono (by omega) (fun _ h => h) this

theorem paramA_run (K1 b : ℕ) (hE : Emb Q b (paramA K1)) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (q : ℕ) (h2 : S.cfg.ptrs 2 = q) :
    Reach Q d f 5 S (fun S' => S'.cfg.pc = b + 5 ∧ Fr S S' [] [9, 10, 11, 12, 25] ∧
      S'.cfg.regs 9 = q ∧ S'.cfg.regs 10 = (q ^ 2 : ℕ) ∧ S'.cfg.regs 25 = (K1 * q ^ 3 : ℕ)) := by
  have q0 : Q[b]? = some (.pointerReal 9 2) := emb_at0 hE (by simp [paramA])
  have q1 : Q[b + 1]? = some (.core (.mul 10 9 9)) := hE 1 (by simp [paramA])
  have q2 : Q[b + 2]? = some (.core (.mul 11 10 9)) := hE 2 (by simp [paramA])
  have q3 : Q[b + 3]? = some (.core (.const 12 ((K1 : ℚ) : ℝ))) := hE 3 (by simp [paramA])
  have q4 : Q[b + 4]? = some (.core (.mul 25 12 11)) := hE 4 (by simp [paramA])
  apply reach_exact 5
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q0, q1, q2, q3, q4, RAMStep, List.getElem?_map, Instr.coreOf,
    State.next, h2, fr_iff (Fr.refl ho [] [9, 10, 11, 12, 25])]
  exact ⟨by ring, Or.inl (by ring)⟩

theorem paramB_run (S1 b : ℕ) (hE : Emb Q b (paramB S1 b)) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (q k' : ℕ) (h1 : S.cfg.ptrs 1 = n) (h22 : S.cfg.ptrs 22 = k')
    (h9 : S.cfg.regs 9 = q) :
    Reach Q d f 6 S (fun S' => S'.cfg.pc = b + 6 ∧ Fr S S' [3, 15] [12, 25] ∧
      S'.cfg.ptrs 3 = (min n k' : ℕ) ∧ S'.cfg.regs 25 = (S1 * q : ℕ)) := by
  have q0 : Q[b]? = some (.core (.pcopy 15 22)) := emb_at0 hE (by simp [paramB])
  have q1 : Q[b + 1]? = some (.core (.pcopy 3 1)) := hE 1 (by simp [paramB])
  have q2 : Q[b + 2]? = some (.core (.pjle 1 15 (b + 4))) := hE 2 (by simp [paramB])
  have q3 : Q[b + 3]? = some (.core (.pcopy 3 15)) := hE 3 (by simp [paramB])
  have q4 : Q[b + 4]? = some (.core (.const 12 ((S1 : ℚ) : ℝ))) := hE 4 (by simp [paramB])
  have q5 : Q[b + 5]? = some (.core (.mul 25 12 9)) := hE 5 (by simp [paramB])
  by_cases hc : n ≤ k'
  · apply reach_mono (show 5 ≤ 6 by norm_num) (fun _ h => h)
    apply reach_exact 5
    have hc' : (n : ℤ) ≤ k' := by exact_mod_cast hc
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp (config := {contextual := true}) [step, ho, hpc, q0, q1, q2, q4, q5, RAMStep, List.getElem?_map, Instr.coreOf,
      State.next, h1, h22, h9, hc', fr_iff (Fr.refl ho [3, 15] [12, 25]), hc]
  · apply reach_exact 6
    have hc' : ¬ (n : ℤ) ≤ k' := by exact_mod_cast hc
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp (config := {contextual := true}) [step, ho, hpc, q0, q1, q2, q3, q4, q5, RAMStep, List.getElem?_map, Instr.coreOf,
      State.next, h1, h22, h9, hc', fr_iff (Fr.refl ho [3, 15] [12, 25])]
    omega

theorem paramC_run (R1 b : ℕ) (hE : Emb Q b (paramC R1)) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (q s : ℕ) (h22 : S.cfg.ptrs 22 = s) (h10 : S.cfg.regs 10 = (q ^ 2 : ℕ)) :
    Reach Q d f 3 S (fun S' => S'.cfg.pc = b + 3 ∧ Fr S S' [4] [12, 25] ∧
      S'.cfg.ptrs 4 = s ∧ S'.cfg.regs 25 = (R1 * q ^ 2 : ℕ)) := by
  have q0 : Q[b]? = some (.core (.pcopy 4 22)) := emb_at0 hE (by simp [paramC])
  have q1 : Q[b + 1]? = some (.core (.const 12 ((R1 : ℚ) : ℝ))) := hE 1 (by simp [paramC])
  have q2 : Q[b + 2]? = some (.core (.mul 25 12 10)) := hE 2 (by simp [paramC])
  apply reach_exact 3
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q0, q1, q2, RAMStep, List.getElem?_map,
    Instr.coreOf, State.next, h22, h10, fr_iff (Fr.refl ho [4] [12, 25])]

theorem paramD_run (b : ℕ) (hE : Emb Q b paramD) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (r : ℕ) (h22 : S.cfg.ptrs 22 = r) :
    Reach Q d f 1 S (fun S' => S'.cfg.pc = b + 1 ∧ Fr S S' [5] [] ∧ S'.cfg.ptrs 5 = r) := by
  have q0 : Q[b]? = some (.core (.pcopy 5 22)) := emb_at0 hE (by simp [paramD])
  apply reach_exact 1
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q0, RAMStep, List.getElem?_map,
    Instr.coreOf, State.next, h22, fr_iff (Fr.refl ho [5] [])]

theorem mloop_run (b : ℕ) (hE : Emb Q b (mloopCode b)) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (h1 : S.cfg.ptrs 1 = n) :
    Reach Q d f (mOf n * 4 + 3) S (fun S' => S'.cfg.pc = b + 6 ∧ Fr S S' [6, 7] [] ∧
      S'.cfg.ptrs 6 = mOf n ∧ S'.cfg.ptrs 7 = 2 ^ mOf n) := by
  have q0 : Q[b]? = some (.core (.pset 6 0)) := emb_at0 hE (by simp [mloopCode])
  have q1 : Q[b + 1]? = some (.core (.pset 7 1)) := hE 1 (by simp [mloopCode])
  have q2 : Q[b + 2]? = some (.core (.pjle 1 7 (b + 6))) := hE 2 (by simp [mloopCode])
  have q3 : Q[b + 3]? = some (.pointerAdd 7 7 7) := hE 3 (by simp [mloopCode])
  have q4 : Q[b + 4]? = some (.core (.pinc 6)) := hE 4 (by simp [mloopCode])
  have q5 : Q[b + 5]? = some (.core (.pjle 0 0 (b + 2))) := hE 5 (by simp [mloopCode])
  let Inv : ℕ → State → Prop := fun i S' =>
    S'.cfg.pc = b + 2 ∧ Fr S S' [6, 7] [] ∧ S'.cfg.ptrs 6 = i ∧ S'.cfg.ptrs 7 = 2 ^ i
  have h0 : Reach Q d f 2 S (Inv 0) := by
    apply reach_exact 2
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp (config := {contextual := true}) [step, ho, hpc, q0, q1, RAMStep, List.getElem?_map,
      Instr.coreOf, Inv, fr_iff (Fr.refl ho [6, 7] [])]
  have hit : ∀ i < mOf n, ∀ S', Inv i S' → Reach Q d f 4 S' (Inv (i + 1)) := by
    rintro i hi S' ⟨hpc', hF, h6, h7⟩
    apply reach_exact 4
    have h1' : S'.cfg.ptrs 1 = n := (hF.ptrs 1 (by decide)).trans h1
    have hlt : ¬ (n : ℤ) ≤ 2 ^ i := by
      have := mOf_min n i hi
      rw [not_le]; exact_mod_cast this
    have ho' := hF.out
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp (config := {contextual := true}) [step, ho', hpc', q2, q3, q4, q5, RAMStep, List.getElem?_map, Instr.coreOf,
      State.next, h1', h6, h7, hlt, Inv, fr_iff hF]
    ring
  have hex : ∀ S', Inv (mOf n) S' → Reach Q d f 1 S'
      (fun S' => S'.cfg.pc = b + 6 ∧ Fr S S' [6, 7] [] ∧
        S'.cfg.ptrs 6 = mOf n ∧ S'.cfg.ptrs 7 = 2 ^ mOf n) := by
    rintro S' ⟨hpc', hF, h6, h7⟩
    apply reach_exact 1
    have h1' : S'.cfg.ptrs 1 = n := (hF.ptrs 1 (by decide)).trans h1
    have hge : (n : ℤ) ≤ 2 ^ mOf n := by exact_mod_cast mOf_spec n
    have ho' := hF.out
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp (config := {contextual := true}) [step, ho', hpc', q2, RAMStep, List.getElem?_map, Instr.coreOf, State.next, h1', h7, hge,
      fr_iff hF, h6]
  have := reach_bind h0 (reach_loop_exit (mOf n) hit hex)
  exact reach_mono (by omega) (fun _ h => h) this

theorem layout_run (b : ℕ) (hE : Emb Q b layoutCode) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) (k s : ℕ) (h0 : S.cfg.ptrs 0 = 0) (h1 : S.cfg.ptrs 1 = n)
    (h3 : S.cfg.ptrs 3 = k) (h4 : S.cfg.ptrs 4 = s) (h12 : S.cfg.ptrs 12 = 1) :
    Reach Q d f 9 S (fun S' => S'.cfg.pc = b + 9 ∧ Fr S S' [8, 9, 10, 11, 13, 23, 24, 25] [] ∧
      S'.cfg.ptrs 13 = (k : ℤ) - 1 ∧ S'.cfg.ptrs 9 = -((n : ℤ) + s) ∧
      S'.cfg.ptrs 10 = -2 * ((n : ℤ) + s) ∧ S'.cfg.ptrs 11 = -3 * ((n : ℤ) + s) ∧
      S'.cfg.ptrs 25 = 0 ∧ S'.cfg.ptrs 24 = (k : ℤ) - 1 ∧ S'.cfg.ptrs 23 = 1) := by
  have q0 : Q[b]? = some (.core (.pcopy 13 3)) := emb_at0 hE (by simp [layoutCode])
  have q1 : Q[b + 1]? = some (.core (.pdec 13)) := hE 1 (by simp [layoutCode])
  have q2 : Q[b + 2]? = some (.pointerAdd 8 1 4) := hE 2 (by simp [layoutCode])
  have q3 : Q[b + 3]? = some (.pointerSub 9 0 8) := hE 3 (by simp [layoutCode])
  have q4 : Q[b + 4]? = some (.pointerAdd 10 9 9) := hE 4 (by simp [layoutCode])
  have q5 : Q[b + 5]? = some (.pointerAdd 11 10 9) := hE 5 (by simp [layoutCode])
  have q6 : Q[b + 6]? = some (.core (.pset 25 0)) := hE 6 (by simp [layoutCode])
  have q7 : Q[b + 7]? = some (.core (.pcopy 24 13)) := hE 7 (by simp [layoutCode])
  have q8 : Q[b + 8]? = some (.core (.pcopy 23 12)) := hE 8 (by simp [layoutCode])
  apply reach_exact 9
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q0, q1, q2, q3, q4, q5, q6, q7, q8, RAMStep, List.getElem?_map,
    Instr.coreOf, State.next, h0, h1, h3, h4, h12, fr_iff (Fr.refl ho [8, 9, 10, 11, 13, 23, 24, 25] [])]
  all_goals first | ring1 | simp | omega

end MTSPEst

end

section

/-! The global invariant and the run of the prefix. -/

open scoped Classical

namespace MTSPEst
open SublinearSteiner SmaleNinth

/-- Global invariant after the prefix. -/
structure Glob (K1 S1 R1 n : ℕ) (S : State) : Prop where
  out : S.output = none
  p0 : S.cfg.ptrs 0 = 0
  p1 : S.cfg.ptrs 1 = n
  p4 : S.cfg.ptrs 4 = sOf S1 n
  p5 : S.cfg.ptrs 5 = rOf R1 n
  p6 : S.cfg.ptrs 6 = mOf n
  p7 : S.cfg.ptrs 7 = 2 ^ mOf n
  p9 : S.cfg.ptrs 9 = -(LOf S1 n : ℤ)
  p10 : S.cfg.ptrs 10 = -2 * (LOf S1 n : ℤ)
  p11 : S.cfg.ptrs 11 = -3 * (LOf S1 n : ℤ)
  p12 : S.cfg.ptrs 12 = 1
  p13 : S.cfg.ptrs 13 = (kOf K1 n - 1 : ℕ)
  r0 : S.cfg.regs 0 = 0
  ones : ∀ u : ℕ, u < n → S.imem (1 + u) = 1

/-- The pointers of the global invariant. -/
def gptrs : List ℕ := [0, 1, 4, 5, 6, 7, 9, 10, 11, 12, 13]

lemma Glob.transfer {K1 S1 R1 n : ℕ} {S S' : State} (hG : Glob K1 S1 R1 n S)
    (ho : S'.output = none) (hp : ∀ j ∈ gptrs, S'.cfg.ptrs j = S.cfg.ptrs j)
    (hr : S'.cfg.regs 0 = S.cfg.regs 0) (hi : ∀ u : ℕ, u < n → S'.imem (1 + u) = S.imem (1 + u)) :
    Glob K1 S1 R1 n S' := by
  refine ⟨ho, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp 0 (by decide)]; exact hG.p0
  · rw [hp 1 (by decide)]; exact hG.p1
  · rw [hp 4 (by decide)]; exact hG.p4
  · rw [hp 5 (by decide)]; exact hG.p5
  · rw [hp 6 (by decide)]; exact hG.p6
  · rw [hp 7 (by decide)]; exact hG.p7
  · rw [hp 9 (by decide)]; exact hG.p9
  · rw [hp 10 (by decide)]; exact hG.p10
  · rw [hp 11 (by decide)]; exact hG.p11
  · rw [hp 12 (by decide)]; exact hG.p12
  · rw [hp 13 (by decide)]; exact hG.p13
  · rw [hr]; exact hG.r0
  · intro u hu; rw [hi u hu]; exact hG.ones u hu

lemma Glob.of_Fr {K1 S1 R1 n : ℕ} {S S' : State} {ps rs : List ℕ} (hG : Glob K1 S1 R1 n S)
    (hF : Fr S S' ps rs) (hps : ∀ j ∈ gptrs, j ∉ ps) (hrs : 0 ∉ rs) : Glob K1 S1 R1 n S' :=
  hG.transfer hF.out (fun j hj => hF.ptrs j (hps j hj)) (hF.regs 0 hrs)
    (fun u _ => by rw [hF.imem])

lemma kOf_pos (K1 n : ℕ) (hK : 1 ≤ K1) (hn : 1 ≤ n) : 1 ≤ kOf K1 n := by
  unfold kOf
  have := qOf_pos n
  have : 1 ≤ qOf n ^ 3 := Nat.one_le_pow _ _ (by omega)
  have : 1 ≤ K1 * qOf n ^ 3 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

lemma kOf_le (K1 n : ℕ) : kOf K1 n ≤ n := min_le_left _ _

section init
variable {n : ℕ}

lemma init_imem0 : (initState (Finset.univ : Finset (Fin n))).imem 0 = n := by simp [initState]

lemma init_ones (u : ℕ) (hu : u < n) : (initState (Finset.univ : Finset (Fin n))).imem (1 + u) = 1 := by
  simp only [initState]
  rw [if_neg (by omega), if_pos ⟨⟨u, hu⟩, by simp, Finset.mem_univ _⟩]

lemma init_neg (z : ℤ) (hz : z < 0) : (initState (Finset.univ : Finset (Fin n))).imem z = 0 := by
  simp only [initState]
  rw [if_neg (by omega), if_neg]
  rintro ⟨v, hv, -⟩
  omega

end init

variable {Q : Program} {n : ℕ} {d : Fin n → Fin n → ℝ} {f : ℕ → Bool}

/-- Step bound of the prefix. -/
noncomputable def preB (K1 S1 R1 n : ℕ) : ℕ :=
  4 + (qOf n * 8 + 7) + 5 + (K1 * qOf n ^ 3 * 5 + 4) + 6 + (S1 * qOf n * 5 + 4) + 3 +
    (R1 * qOf n ^ 2 * 5 + 4) + 1 + (mOf n * 4 + 3) + 9

theorem prefix_run (K1 S1 R1 : ℕ) (hK : 1 ≤ K1) (hE : Emb Q 0 (pre0 K1 S1 R1)) (hn : ¬ n ≤ 1) :
    Reach Q d f (preB K1 S1 R1 n) (initState (Finset.univ : Finset (Fin n))) (fun S =>
      S.cfg.pc = 63 ∧ Glob K1 S1 R1 n S ∧ S.cfg.ptrs 25 = 0 ∧
      S.cfg.ptrs 24 = (kOf K1 n - 1 : ℕ) ∧ S.cfg.ptrs 23 = 1 ∧
      S.imem = (initState (Finset.univ : Finset (Fin n))).imem ∧ S.coins = 0 ∧ S.queries = 0) := by
  set I := initState (Finset.univ : Finset (Fin n)) with hI
  obtain ⟨e0, hE⟩ := emb_split hE (show 0 + (setupCode 0).length = 6 from rfl)
  obtain ⟨e1, hE⟩ := emb_split hE (show 6 + (qloopCode 6).length = 15 from rfl)
  obtain ⟨e2, hE⟩ := emb_split hE (show 15 + (paramA K1).length = 20 from rfl)
  obtain ⟨e3, hE⟩ := emb_split hE (show 20 + (countUpCode 20).length = 26 from rfl)
  obtain ⟨e4, hE⟩ := emb_split hE (show 26 + (paramB S1 26).length = 32 from rfl)
  obtain ⟨e5, hE⟩ := emb_split hE (show 32 + (countUpCode 32).length = 38 from rfl)
  obtain ⟨e6, hE⟩ := emb_split hE (show 38 + (paramC R1).length = 41 from rfl)
  obtain ⟨e7, hE⟩ := emb_split hE (show 41 + (countUpCode 41).length = 47 from rfl)
  obtain ⟨e8, hE⟩ := emb_split hE (show 47 + paramD.length = 48 from rfl)
  obtain ⟨e9, e10⟩ := emb_split hE (show 48 + (mloopCode 48).length = 54 from rfl)
  have hI0 : I.output = none := rfl
  -- setup
  obtain ⟨T1, hT1, hpc1, hF1, h1n, h112⟩ :=
    setup_run (d := d) (f := f) 0 e0 I rfl hI0 rfl init_imem0 hn
  generalize hS1 : (step Q d f)^[T1] I = Z1 at hpc1 hF1 h1n h112
  -- q loop
  obtain ⟨T2, hT2, hpc2, hF2, h2q⟩ := qloop_run (d := d) (f := f) 6 e1 Z1 hpc1 hF1.out h1n
  generalize hS2 : (step Q d f)^[T2] Z1 = Z2 at hpc2 hF2 h2q
  -- paramA
  obtain ⟨T3, hT3, hpc3, hF3, h3r9, h3r10, h3r25⟩ :=
    paramA_run (d := d) (f := f) K1 15 e2 Z2 hpc2 hF2.out (qOf n) h2q
  generalize hS3 : (step Q d f)^[T3] Z2 = Z3 at hpc3 hF3 h3r9 h3r10 h3r25
  -- countUp k'
  obtain ⟨T4, hT4, hpc4, hF4, h4c⟩ :=
    countUp_run (d := d) (f := f) 20 e3 Z3 hpc3 hF3.out _ h3r25
  generalize hS4 : (step Q d f)^[T4] Z3 = Z4 at hpc4 hF4 h4c
  -- paramB
  have h4n : Z4.cfg.ptrs 1 = n := by
    rw [hF4.ptrs 1 (by decide), hF3.ptrs 1 (by decide), hF2.ptrs 1 (by decide)]; exact h1n
  have h4r9 : Z4.cfg.regs 9 = qOf n := by rw [hF4.regs 9 (by decide)]; exact h3r9
  obtain ⟨T5, hT5, hpc5, hF5, h5k, h5r25⟩ :=
    paramB_run (d := d) (f := f) S1 26 e4 Z4 hpc4 hF4.out (qOf n) _ h4n h4c h4r9
  generalize hS5 : (step Q d f)^[T5] Z4 = Z5 at hpc5 hF5 h5k h5r25
  -- countUp s
  obtain ⟨T6, hT6, hpc6, hF6, h6c⟩ :=
    countUp_run (d := d) (f := f) 32 e5 Z5 hpc5 hF5.out _ h5r25
  generalize hS6 : (step Q d f)^[T6] Z5 = Z6 at hpc6 hF6 h6c
  -- paramC
  have h6r10 : Z6.cfg.regs 10 = (qOf n ^ 2 : ℕ) := by
    rw [hF6.regs 10 (by decide), hF5.regs 10 (by decide), hF4.regs 10 (by decide)]; exact h3r10
  obtain ⟨T7, hT7, hpc7, hF7, h7s, h7r25⟩ :=
    paramC_run (d := d) (f := f) R1 38 e6 Z6 hpc6 hF6.out (qOf n) _ h6c h6r10
  generalize hS7 : (step Q d f)^[T7] Z6 = Z7 at hpc7 hF7 h7s h7r25
  -- countUp r
  obtain ⟨T8, hT8, hpc8, hF8, h8c⟩ :=
    countUp_run (d := d) (f := f) 41 e7 Z7 hpc7 hF7.out _ h7r25
  generalize hS8 : (step Q d f)^[T8] Z7 = Z8 at hpc8 hF8 h8c
  -- paramD
  obtain ⟨T9, hT9, hpc9, hF9, h9r⟩ := paramD_run (d := d) (f := f) 47 e8 Z8 hpc8 hF8.out _ h8c
  generalize hS9 : (step Q d f)^[T9] Z8 = Z9 at hpc9 hF9 h9r
  -- m loop
  have h9n : Z9.cfg.ptrs 1 = n := by
    rw [hF9.ptrs 1 (by decide), hF8.ptrs 1 (by decide), hF7.ptrs 1 (by decide),
      hF6.ptrs 1 (by decide), hF5.ptrs 1 (by decide)]; exact h4n
  obtain ⟨T10, hT10, hpc10, hF10, h10m, h10N⟩ :=
    mloop_run (d := d) (f := f) 48 e9 Z9 hpc9 hF9.out h9n
  generalize hS10 : (step Q d f)^[T10] Z9 = Z10 at hpc10 hF10 h10m h10N
  -- layout
  have h10n : Z10.cfg.ptrs 1 = n := by rw [hF10.ptrs 1 (by decide)]; exact h9n
  have h10_0 : Z10.cfg.ptrs 0 = 0 := by
    rw [hF10.ptrs 0 (by decide), hF9.ptrs 0 (by decide), hF8.ptrs 0 (by decide),
      hF7.ptrs 0 (by decide), hF6.ptrs 0 (by decide), hF5.ptrs 0 (by decide),
      hF4.ptrs 0 (by decide), hF3.ptrs 0 (by decide), hF2.ptrs 0 (by decide),
      hF1.ptrs 0 (by decide)]; rfl
  have h10k : Z10.cfg.ptrs 3 = kOf K1 n := by
    rw [hF10.ptrs 3 (by decide), hF9.ptrs 3 (by decide), hF8.ptrs 3 (by decide),
      hF7.ptrs 3 (by decide), hF6.ptrs 3 (by decide), h5k]; rfl
  have h10s : Z10.cfg.ptrs 4 = sOf S1 n := by
    rw [hF10.ptrs 4 (by decide), hF9.ptrs 4 (by decide), hF8.ptrs 4 (by decide), h7s]; rfl
  have h10_12 : Z10.cfg.ptrs 12 = 1 := by
    rw [hF10.ptrs 12 (by decide), hF9.ptrs 12 (by decide), hF8.ptrs 12 (by decide),
      hF7.ptrs 12 (by decide), hF6.ptrs 12 (by decide), hF5.ptrs 12 (by decide),
      hF4.ptrs 12 (by decide), hF3.ptrs 12 (by decide), hF2.ptrs 12 (by decide)]; exact h112
  obtain ⟨T11, hT11, hpc11, hF11, h11_13, h11_9, h11_10, h11_11, h11_25, h11_24, h11_23⟩ :=
    layout_run (d := d) (f := f) 54 e10 Z10 hpc10 hF10.out _ _ h10_0 h10n h10k h10s h10_12
  generalize hS11 : (step Q d f)^[T11] Z10 = Z11 at hpc11 hF11 h11_13 h11_9 h11_10 h11_11 h11_25 h11_24 h11_23
  have hk1 := kOf_pos K1 n hK (by omega)
  have hFall := (((((((((hF1.trans hF2).trans hF3).trans hF4).trans hF5).trans hF6).trans hF7).trans
    hF8).trans hF9).trans hF10).trans hF11
  have c := iter_trans hS1 hS2
  have c := iter_trans c hS3
  have c := iter_trans c hS4
  have c := iter_trans c hS5
  have c := iter_trans c hS6
  have c := iter_trans c hS7
  have c := iter_trans c hS8
  have c := iter_trans c hS9
  have c := iter_trans c hS10
  have c := iter_trans c hS11
  refine reach_of_iter _ ?_ c ?_
  · unfold preB; omega
  have hkz : ((kOf K1 n - 1 : ℕ) : ℤ) = (kOf K1 n : ℤ) - 1 := by push_cast [hk1]; ring
  refine ⟨hpc11, ⟨hFall.out, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, h11_25, ?_, h11_23,
    hFall.imem, hFall.coins, hFall.queries⟩
  · rw [hF11.ptrs 0 (by decide)]; exact h10_0
  · rw [hF11.ptrs 1 (by decide)]; exact h10n
  · rw [hF11.ptrs 4 (by decide)]; exact h10s
  · rw [hF11.ptrs 5 (by decide), hF10.ptrs 5 (by decide), h9r]; rfl
  · rw [hF11.ptrs 6 (by decide), h10m]
  · rw [hF11.ptrs 7 (by decide), h10N]
  · rw [h11_9]; simp [LOf]
  · rw [h11_10]; simp [LOf]
  · rw [h11_11]; simp [LOf]
  · rw [hF11.ptrs 12 (by decide)]; exact h10_12
  · rw [h11_13, hkz]
  · rw [hFall.regs 0 (by decide)]; rfl
  · intro u hu; rw [hFall.imem]; exact init_ones u hu
  · rw [h11_24, hkz]

end MTSPEst

end

section

/-! A call of the greedy-growth subroutine (argument setup + `growCode`). All uses of
`MTSPGrow.grow_run` are in this file. -/

open scoped Classical

namespace MTSPEst
open SublinearSteiner SmaleNinth MTSPMst

variable {Q : Program} {n : ℕ} {d : Fin n → Fin n → ℝ} {f : ℕ → Bool}

/-- Step-bound constant of the subroutine: `grow_run` gives `≤ growC * (K + 1) * (n + 1)`. -/
def growC : ℕ := 40

lemma callArgs_run (b : ℕ) (hE : Emb Q b callArgs) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) :
    let S' := (step Q d f)^[8] S
    S'.cfg.pc = b + 8 ∧ S'.output = none ∧ S'.coins = S.coins ∧ S'.queries = S.queries ∧
    S'.imem = S.imem ∧ S'.cfg.mem = S.cfg.mem ∧ S'.cfg.regs = S.cfg.regs ∧
    (∀ j, j < 100 → S'.cfg.ptrs j = S.cfg.ptrs j) ∧
    S'.cfg.ptrs 100 = S.cfg.ptrs 1 ∧ S'.cfg.ptrs 101 = S.cfg.ptrs 25 ∧
    S'.cfg.ptrs 102 = S.cfg.ptrs 24 ∧ S'.cfg.ptrs 103 = S.cfg.ptrs 23 ∧
    S'.cfg.ptrs 104 = S.cfg.ptrs 9 ∧ S'.cfg.ptrs 105 = S.cfg.ptrs 9 ∧
    S'.cfg.ptrs 106 = S.cfg.ptrs 10 ∧ S'.cfg.ptrs 107 = S.cfg.ptrs 10 := by
  intro S'
  have q0 : Q[b]? = some (.core (.pcopy 100 1)) := emb_at0 hE (by simp [callArgs])
  have q1 : Q[b + 1]? = some (.core (.pcopy 101 25)) := hE 1 (by simp [callArgs])
  have q2 : Q[b + 2]? = some (.core (.pcopy 102 24)) := hE 2 (by simp [callArgs])
  have q3 : Q[b + 3]? = some (.core (.pcopy 103 23)) := hE 3 (by simp [callArgs])
  have q4 : Q[b + 4]? = some (.core (.pcopy 104 9)) := hE 4 (by simp [callArgs])
  have q5 : Q[b + 5]? = some (.core (.pcopy 105 9)) := hE 5 (by simp [callArgs])
  have q6 : Q[b + 6]? = some (.core (.pcopy 106 10)) := hE 6 (by simp [callArgs])
  have q7 : Q[b + 7]? = some (.core (.pcopy 107 10)) := hE 7 (by simp [callArgs])
  simp only [S', Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q0, q1, q2, q3, q4, q5, q6, q7, RAMStep,
    List.getElem?_map, Instr.coreOf, State.next, Function.update_apply]
  intro j hj
  simp [show j ≠ 100 by omega, show j ≠ 101 by omega, show j ≠ 102 by omega, show j ≠ 103 by omega,
    show j ≠ 104 by omega, show j ≠ 105 by omega, show j ≠ 106 by omega, show j ≠ 107 by omega]

theorem call_run (K1 S1 R1 : ℕ) (mode : Bool) (b : ℕ) (hE : Emb Q b (callCode mode b))
    (hd : DoublingMST.IsMetric d) (S : State) (hpc : S.cfg.pc = b) (hG : Glob K1 S1 R1 n S)
    (start : Fin n) (K : ℕ) (MB : ℤ) (h25 : S.cfg.ptrs 25 = (start : ℕ)) (h24 : S.cfg.ptrs 24 = K)
    (h23 : S.cfg.ptrs 23 = MB) (hK : K ≤ LOf S1 n) (hMB : MB = 1 ∨ MB = -3 * (LOf S1 n : ℤ)) :
    Reach Q d f (8 + growC * (K + 1) * (n + 1)) S (fun S' =>
      S'.cfg.pc = b + 8 + (MTSPGrow.growCode mode (b + 8)).length ∧ Glob K1 S1 R1 n S' ∧
      S'.coins = S.coins ∧ S'.queries ≤ S.queries + (K + 1) * n ∧
      S'.cfg.ptrs 108 = (grun d mode (MTSPGrow.maskOf S MB) start K).2.length ∧
      (∀ j (hj : j < (grun d mode (MTSPGrow.maskOf S MB) start K).2.length),
        S'.imem (-2 * (LOf S1 n : ℤ) + j) = (((grun d mode (MTSPGrow.maskOf S MB) start K).2[j]).1 : ℕ) ∧
        S'.cfg.mem (-2 * (LOf S1 n : ℤ) + j) = ((grun d mode (MTSPGrow.maskOf S MB) start K).2[j]).2) ∧
      (∀ u : Fin n, S'.cfg.mem (-(LOf S1 n : ℤ) + u) = (grun d mode (MTSPGrow.maskOf S MB) start K).1.key u) ∧
      (∀ z : ℤ, ¬ (-(LOf S1 n : ℤ) ≤ z ∧ z < -(LOf S1 n : ℤ) + n) →
        ¬ (-2 * (LOf S1 n : ℤ) ≤ z ∧ z < -2 * (LOf S1 n : ℤ) + K) → S'.imem z = S.imem z) ∧
      (∀ j, j < 100 → S'.cfg.ptrs j = S.cfg.ptrs j) ∧
      (∀ j, j < 100 → S'.cfg.regs j = S.cfg.regs j)) := by
  obtain ⟨eA, eG⟩ := emb_split hE (show b + callArgs.length = b + 8 from rfl)
  obtain ⟨p8, o8, c8, q8, i8, m8, r8, pp8, a100, a101, a102, a103, a104, a105, a106, a107⟩ :=
    callArgs_run (d := d) (f := f) b eA S hpc hG.out
  generalize hS8 : (step Q d f)^[8] S = S8 at p8 o8 c8 q8 i8 m8 r8 pp8 a100 a101 a102 a103 a104 a105 a106 a107
  have hL : (LOf S1 n : ℤ) = n + (sOf S1 n : ℤ) := by simp [LOf]
  have hs : (0 : ℤ) ≤ sOf S1 n := by positivity
  have hK' : (K : ℤ) ≤ LOf S1 n := by exact_mod_cast hK
  have hMB' : MTSPGrow.maskOf (n := n) S8 MB = MTSPGrow.maskOf S MB := by
    funext u; simp [MTSPGrow.maskOf, i8]
  obtain ⟨T, hT, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ :=
    MTSPGrow.grow_run mode Q (b + 8) eG d hd f S8 start K MB (-(LOf S1 n : ℤ)) (-(LOf S1 n : ℤ))
      (-2 * (LOf S1 n : ℤ)) (-2 * (LOf S1 n : ℤ)) p8 o8 (by rw [a100, hG.p1])
      (by rw [a101, h25]) (by rw [a102, h24]) (by rw [a103, h23]) (by rw [a104, hG.p9])
      (by rw [a105, hG.p9]) (by rw [a106, hG.p10]) (by rw [a107, hG.p10])
      (by rcases hMB with h | h <;> subst h <;> omega) (by rcases hMB with h | h <;> subst h <;> omega)
      (by omega) (by omega)
  rw [hMB'] at g5 g6 g7
  generalize hS' : (step Q d f)^[T] S8 = S' at g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12
  have c := iter_trans hS8 hS'
  refine reach_of_iter _ (by unfold growC; omega) c ⟨g1, ?_, by rw [g3, c8], by rw [q8] at g4; exact g4,
    g5, g6, g7, fun z h1 h2 => by rw [g8 z h1 h2, i8], fun j hj => by rw [g10 j (Or.inl hj), pp8 j hj],
    fun j hj => by rw [g12 j (Or.inl hj), r8]⟩
  refine hG.transfer g2 (fun j hj => ?_) (by rw [g12 0 (by omega), r8]) (fun u hu => ?_)
  · have : j < 100 := by simp [gptrs] at hj; omega
    rw [g10 j (Or.inl this), pp8 j this]
  · rw [g8 _ (by omega) (by omega), i8]

end MTSPEst

end

section

/-! Layout of `estProg` and small helper blocks. -/

open scoped Classical

namespace MTSPEst
open SublinearSteiner SmaleNinth MTSPMst

variable {Q : Program} {n : ℕ} {d : Fin n → Fin n → ℝ} {f : ℕ → Bool}

theorem pcopy_run (dst src b : ℕ) (hE : Emb Q b [.core (.pcopy dst src)]) (S : State)
    (hpc : S.cfg.pc = b) (ho : S.output = none) :
    Reach Q d f 1 S (fun S' => S'.cfg.pc = b + 1 ∧ Fr S S' [dst] [] ∧
      S'.cfg.ptrs dst = S.cfg.ptrs src) := by
  have q0 : Q[b]? = some (.core (.pcopy dst src)) := emb_at0 hE (by simp)
  apply reach_exact 1
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q0, RAMStep, List.getElem?_map,
    Instr.coreOf, fr_iff (Fr.refl ho [dst] []), Function.update_apply]

theorem call2args_run (b : ℕ) (hE : Emb Q b call2Args) (S : State) (hpc : S.cfg.pc = b)
    (ho : S.output = none) :
    Reach Q d f 3 S (fun S' => S'.cfg.pc = b + 3 ∧ Fr S S' [23, 24, 25] [] ∧
      S'.cfg.ptrs 25 = 0 ∧ S'.cfg.ptrs 24 = S.cfg.ptrs 13 ∧ S'.cfg.ptrs 23 = S.cfg.ptrs 11) := by
  have q0 : Q[b]? = some (.core (.pset 25 0)) := emb_at0 hE (by simp [call2Args])
  have q1 : Q[b + 1]? = some (.core (.pcopy 24 13)) := hE 1 (by simp [call2Args])
  have q2 : Q[b + 2]? = some (.core (.pcopy 23 11)) := hE 2 (by simp [call2Args])
  apply reach_exact 3
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp (config := {contextual := true}) [step, ho, hpc, q0, q1, q2, RAMStep, List.getElem?_map,
    Instr.coreOf, State.next, fr_iff (Fr.refl ho [23, 24, 25] [])]

lemma grun_len_le (d : Fin n → Fin n → ℝ) (mode : Bool) (mask : Fin n → Bool) (start : Fin n) :
    ∀ j, (grun d mode mask start j).2.length ≤ j
  | 0 => by simp [grun]
  | j + 1 => by
    have := grun_len_le d mode mask start j
    simp only [grun]
    split <;> simp <;> omega

/-- All code blocks of `estProg` at their positions. -/
structure Layout (K1 S1 R1 : ℕ) (cinv scale : ℚ) (Q : Program) : Prop where
  pre : Emb Q 0 (pre0 K1 S1 R1)
  c1 : Emb Q 63 (callCode true 63)
  a1p : Emb Q b1 [.core (.pcopy 16 108)]
  t0 : Emb Q (b1 + 1) (t0Code (b1 + 1))
  t1 : Emb Q (b1 + 12) (t1Code cinv)
  mark : Emb Q (b1 + 14) (markCode (b1 + 14))
  c2a : Emb Q (b1 + 24) call2Args
  c2 : Emb Q g2 (callCode false g2)
  a2p : Emb Q b2 [.core (.pcopy 17 108)]
  ap : Emb Q (b2 + 1) (apCode (b2 + 1))
  hi : Emb Q (b2 + 12) hinitCode
  hd : Emb Q (b2 + 14) [.core (.pjle 5 14 (b3 + 35))]
  coin : Emb Q (b2 + 15) (coinCode (b2 + 15))
  test : Emb Q (b2 + 24) (testCode (b3 + 33))
  c3 : Emb Q g3 (callCode false g3)
  a3p : Emb Q b3 [.core (.pcopy 18 108)]
  hl : Emb Q (b3 + 1) (hloopCode (b3 + 1))
  tl : Emb Q (b3 + 32) (tailCode (b2 + 14))
  fin : Emb Q (b3 + 35) (finalCode scale)

theorem layout (K1 S1 R1 : ℕ) (cinv scale : ℚ) : Layout K1 S1 R1 cinv scale (estProg K1 S1 R1 cinv scale) := by
  have hE := emb_self (estProg K1 S1 R1 cinv scale)
  unfold estProg at hE
  obtain ⟨epre, hE⟩ := emb_split hE (show 0 + (pre0 K1 S1 R1).length = 63 from rfl)
  obtain ⟨ec1, hE⟩ := emb_split hE (show 63 + (callCode true 63).length = b1 by
    simp [callCode, callArgs, b1]; omega)
  obtain ⟨eA1, hE⟩ := emb_split hE (show b1 + (A1code cinv b1).length = g2 from rfl)
  obtain ⟨ec2, hE⟩ := emb_split hE (show g2 + (callCode false g2).length = b2 by
    simp [callCode, callArgs, b2]; omega)
  obtain ⟨eA2, hE⟩ := emb_split hE (show b2 + (A2code b2 (b3 + 33) (b3 + 35)).length = g3 from rfl)
  obtain ⟨ec3, eA3⟩ := emb_split hE (show g3 + (callCode false g3).length = b3 by
    simp [callCode, callArgs, b3]; omega)
  obtain ⟨a1p, eA1⟩ := emb_split eA1 (show b1 + 1 = b1 + 1 from rfl)
  obtain ⟨t0, eA1⟩ := emb_split eA1 (show b1 + 1 + (t0Code (b1 + 1)).length = b1 + 12 from rfl)
  obtain ⟨t1, eA1⟩ := emb_split eA1 (show b1 + 12 + (t1Code cinv).length = b1 + 14 from rfl)
  obtain ⟨mk, c2a⟩ := emb_split eA1 (show b1 + 14 + (markCode (b1 + 14)).length = b1 + 24 from rfl)
  obtain ⟨a2p, eA2⟩ := emb_split eA2 (show b2 + 1 = b2 + 1 from rfl)
  obtain ⟨ap, eA2⟩ := emb_split eA2 (show b2 + 1 + (apCode (b2 + 1)).length = b2 + 12 from rfl)
  obtain ⟨hi, eA2⟩ := emb_split eA2 (show b2 + 12 + hinitCode.length = b2 + 14 from rfl)
  obtain ⟨hd, eA2⟩ := emb_split eA2 (show b2 + 14 + 1 = b2 + 15 from rfl)
  obtain ⟨coin, test⟩ := emb_split eA2 (show b2 + 15 + (coinCode (b2 + 15)).length = b2 + 24 from rfl)
  obtain ⟨a3p, eA3⟩ := emb_split eA3 (show b3 + 1 = b3 + 1 from rfl)
  obtain ⟨hl, eA3⟩ := emb_split eA3 (show b3 + 1 + (hloopCode (b3 + 1)).length = b3 + 32 from rfl)
  obtain ⟨tl, fin⟩ := emb_split eA3 (show b3 + 32 + (tailCode (b2 + 14)).length = b3 + 35 from rfl)
  exact ⟨epre, ec1, a1p, t0, t1, mk, c2a, ec2, a2p, ap, hi, hd, coin, test, ec3, a3p, hl, tl, fin⟩

end MTSPEst

end

section

/-! One iteration of the sampling loop. -/

open scoped Classical

namespace MTSPEst
open SublinearSteiner SmaleNinth MTSPMst Finset

variable {n : ℕ}

/-- Invariant at the head of the sampling loop after `i` samples. -/
def OInv (K1 S1 R1 : ℕ) (cinv : ℚ) (d : Fin n → Fin n → ℝ) (h : 0 < n) (f : ℕ → Bool)
    (Q0 : ℕ) (A0 : ℝ) (i : ℕ) (S : State) : Prop :=
  S.cfg.pc = b2 + 14 ∧ Glob K1 S1 R1 n S ∧ S.cfg.regs 1 = T1 K1 cinv d h ∧ S.cfg.regs 2 = A0 ∧
    S.cfg.regs 3 = ∑ i' ∈ range i, X K1 S1 cinv d h (MTSPDecode.dec (mOf n) f i') ∧
    S.cfg.ptrs 14 = i ∧ S.coins = i * mOf n ∧ S.queries ≤ Q0 + i * ((sOf S1 n + 1) * n)

/-- Steps of one iteration after the coins. -/
noncomputable def contB (S1 n : ℕ) : ℕ :=
  3 + ((8 + growC * (sOf S1 n + 1) * (n + 1)) + (1 + ((sOf S1 n * 19 + 12) + (3 + 0))))

noncomputable def iterB (S1 n : ℕ) : ℕ := 1 + ((mOf n * 7 + 3) + contB S1 n)

lemma not_mem_gptrs {j : ℕ} (hj : j ∈ gptrs) (l : List ℕ) (hl : ∀ x ∈ l, 14 ≤ x) : j ∉ l := by
  intro h
  have := hl j h
  simp [gptrs] at hj
  omega

theorem outer_iter (K1 S1 R1 : ℕ) (cinv scale : ℚ) {Q : Program}
    (hL : Layout K1 S1 R1 cinv scale Q) {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d)
    (h : 0 < n) (f : ℕ → Bool) (Q0 : ℕ) (A0 : ℝ) (i : ℕ) (hi : i < rOf R1 n) (S : State)
    (hS : OInv K1 S1 R1 cinv d h f Q0 A0 i S) :
    Reach Q d f (iterB S1 n) S (OInv K1 S1 R1 cinv d h f Q0 A0 (i + 1)) := by
  obtain ⟨hpc, hG, h1, h2, h3, h14, hc, hq⟩ := hS
  unfold iterB
  refine reach_bind (head_go (b3 + 35) (b2 + 14) hL.hd S hpc hG.out (rOf R1 n) i hG.p5 h14 hi) ?_
  rintro S1' ⟨hpc1, hF1⟩
  have hG1 := hG.of_Fr hF1 (fun j hj => by simp) (by decide)
  refine reach_bind (coin_run (b2 + 15) hL.coin S1' hpc1 hF1.out (mOf n) hG1.p6) ?_
  rintro S2 ⟨hpc2, hP⟩
  have hcoins1 : S1'.coins = i * mOf n := hF1.coins.trans hc
  have hu : S2.cfg.ptrs 25 = (MTSPDecode.dec (mOf n) f i : ℕ) := by
    rw [hP.p25, hcoins1]; rfl
  have hG2 : Glob K1 S1 R1 n S2 := hG1.transfer hP.out
    (fun j hj => hP.ptrs j (not_mem_gptrs hj _ (by decide))) (hP.regs 0 (by decide))
    (fun u _ => by rw [hP.imem])
  have hr2 : ∀ j, j ≠ 5 → S2.cfg.regs j = S.cfg.regs j := fun j hj =>
    (hP.regs j hj).trans (hF1.regs j (by simp))
  have hp2_14 : S2.cfg.ptrs 14 = i := by
    rw [hP.ptrs 14 (by decide), hF1.ptrs 14 (by simp), h14]
  have hc2 : S2.coins = (i + 1) * mOf n := by rw [hP.coins, hcoins1]; ring
  have hq2 : S2.queries = S.queries := hP.queries.trans hF1.queries
  have hpc2' : S2.cfg.pc = b2 + 24 := by rw [hpc2]
  set u := MTSPDecode.dec (mOf n) f i with hu_def
  by_cases hun : u < n
  · refine reach_mono (B := 3 + ((8 + growC * (sOf S1 n + 1) * (n + 1)) +
      (1 + ((sOf S1 n * 19 + 12) + (3 + 0))))) (by unfold contB; omega) (fun _ h => h) ?_
    refine reach_bind (test_go (b3 + 33) (b2 + 24) hL.test S2 hpc2' hP.out u hG2.p1 hu hun) ?_
    rintro S3 ⟨hpc3, hF3, h24, h23⟩
    have hG3 := hG2.of_Fr hF3 (fun j hj => not_mem_gptrs hj _ (by decide)) (by decide)
    have hmask : MTSPGrow.maskOf (n := n) S3 1 = allOnes := by
      funext v; simp [MTSPGrow.maskOf, allOnes, hG3.ones v v.isLt]
    refine reach_bind (call_run K1 S1 R1 false g3 hL.c3 hd S3 (by rw [hpc3]; rfl) hG3 ⟨u, hun⟩
      (sOf S1 n) 1 (by rw [hF3.ptrs 25 (by decide), hu]) (by rw [h24, hG2.p4])
      (by rw [h23, hG2.p12]) (by simp [LOf]) (Or.inl rfl)) ?_
    rintro S4 ⟨hpc4, hG4, hc4, hq4, h108, hrec, -, -, hpp4, hrr4⟩
    rw [hmask] at h108 hrec
    have hpc4' : S4.cfg.pc = b3 := by rw [hpc4]; rfl
    refine reach_bind (pcopy_run 18 108 b3 hL.a3p S4 hpc4' hG4.out) ?_
    rintro S5 ⟨hpc5, hF5, h18⟩
    have hG5 := hG4.of_Fr hF5 (fun j hj => not_mem_gptrs hj _ (by decide)) (by decide)
    set vals := (run3 S1 d ⟨u, hun⟩).2.map Prod.snd with hvals
    have hT5 : S5.cfg.regs 1 = T1 K1 cinv d h := by
      rw [hF5.regs 1 (by decide), hrr4 1 (by norm_num), hF3.regs 1 (by decide), hr2 1 (by decide), h1]
    refine reach_bind (hloop_run (b3 + 1) hL.hl S5 hpc5 hF5.out (sOf S1 n)
      (run3 S1 d ⟨u, hun⟩).2.length (-2 * (LOf S1 n : ℤ)) (T1 K1 cinv d h) vals hG5.p1 hG5.p4
      (by rw [h18, h108]; rfl) hG5.p10 hT5 hG5.r0 (by simp [vals])
      (fun j hj => by
        rw [hF5.mem, (hrec j hj).2]
        simp only [vals, List.getD_eq_getElem?_getD, List.getElem?_map]
        rw [List.getElem?_eq_getElem hj]; rfl)) ?_
    rintro S6 ⟨hpc6, hF6, h10⟩
    have hpc6' : S6.cfg.pc = b3 + 32 := by rw [hpc6]
    refine reach_bind (tail_run (b2 + 14) (b3 + 32) hL.tl S6 hpc6' hF6.out) ?_
    rintro S7 ⟨hpc7, hF7, h3', h14'⟩
    refine reach_now (B := 0) ⟨hpc7, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hG5.of_Fr hF6 (fun j hj => not_mem_gptrs hj _ (by decide)) (by decide)).of_Fr hF7
        (fun j hj => not_mem_gptrs hj _ (by decide)) (by decide)
    · rw [hF7.regs 1 (by decide), hF6.regs 1 (by decide), hT5]
    · rw [hF7.regs 2 (by decide), hF6.regs 2 (by decide), hF5.regs 2 (by decide),
        hrr4 2 (by norm_num), hF3.regs 2 (by decide), hr2 2 (by decide), h2]
    · rw [h3', h10, hF6.regs 3 (by decide), hF5.regs 3 (by decide), hrr4 3 (by norm_num),
        hF3.regs 3 (by decide), hr2 3 (by decide), h3, sum_range_succ]
      congr 1
      simp only [X, ← hu_def, dif_pos hun]
      rfl
    · rw [h14', hF6.ptrs 14 (by decide), hF5.ptrs 14 (by decide), hpp4 14 (by norm_num),
        hF3.ptrs 14 (by decide), hp2_14]; push_cast; ring
    · rw [hF7.coins, hF6.coins, hF5.coins, hc4, hF3.coins, hc2]
    · rw [hF7.queries, hF6.queries, hF5.queries]
      have := hF3.queries
      rw [Nat.succ_mul]
      omega
  · refine reach_mono (B := 1 + (2 + 0)) (by unfold contB; omega) (fun _ h => h) ?_
    refine reach_bind (test_skip (b3 + 33) (b2 + 24) hL.test S2 hpc2' hP.out u hG2.p1 hu
      (by omega)) ?_
    rintro S3 ⟨hpc3, hF3⟩
    refine reach_bind (tail_skip (b2 + 14) (b3 + 32) hL.tl S3 hpc3 hF3.out) ?_
    rintro S4 ⟨hpc4, hF4, h14'⟩
    refine reach_now (B := 0) ⟨hpc4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hG2.of_Fr hF3 (fun j hj => by simp) (by decide)).of_Fr hF4
        (fun j hj => not_mem_gptrs hj _ (by decide)) (by decide)
    · rw [hF4.regs 1 (by decide), hF3.regs 1 (by decide), hr2 1 (by decide), h1]
    · rw [hF4.regs 2 (by decide), hF3.regs 2 (by decide), hr2 2 (by decide), h2]
    · rw [hF4.regs 3 (by decide), hF3.regs 3 (by decide), hr2 3 (by decide), h3, sum_range_succ]
      simp only [X, ← hu_def, dif_neg hun, add_zero]
    · rw [h14', hF3.ptrs 14 (by decide), hp2_14]; push_cast; ring
    · rw [hF4.coins, hF3.coins, hc2]
    · rw [hF4.queries, hF3.queries, hq2]
      rw [Nat.succ_mul]
      omega

end MTSPEst

end

section

/-! Arithmetic for the step and query bounds. -/

namespace MTSPEst

/-- Constant of the step bound (`growC = 40`: `400 + 85 K1 + 5 S1 + 83 R1 + 59 R1 S1`). -/
def estC (K1 S1 R1 : ℕ) : ℕ :=
  400 + 5 * K1 + 5 * S1 + 43 * R1 + 19 * (R1 * S1) + 2 * (growC * K1) + growC * R1 * S1 + growC * R1

/-- The exact sum of the block step bounds. -/
def totB (G K1 S1 R1 q n k s r m c1 c2 : ℕ) : ℕ :=
  (4 + (q * 8 + 7) + 5 + (K1 * q ^ 3 * 5 + 4) + 6 + (S1 * q * 5 + 4) + 3 + (R1 * q ^ 2 * 5 + 4) + 1 +
    (m * 4 + 3) + 9) +
  (8 + G * (k - 1 + 1) * (n + 1)) + 1 + (n * 8 + 4) + 2 + (c1 * 7 + 4) + 3 +
  (8 + G * (k - 1 + 1) * (n + 1)) + 1 + (c2 * 8 + 4) + 2 +
  (r * (1 + ((m * 7 + 3) + (3 + ((8 + G * (s + 1) * (n + 1)) + (1 + ((s * 19 + 12) + (3 + 0))))))) +
    (1 + 9))

lemma time_le (K1 S1 R1 q n k s r m c1 c2 : ℕ) (hq : 1 ≤ q) (hk1 : 1 ≤ k) (hk : k ≤ n)
    (hkq : k ≤ K1 * q ^ 3) (hs : s = S1 * q) (hr : r = R1 * q ^ 2) (hm : m ≤ n) (hc1 : c1 ≤ k)
    (hc2 : c2 ≤ k) :
    totB growC K1 S1 R1 q n k s r m c1 c2 ≤ estC K1 S1 R1 * (q + 1) ^ 3 * (n + 1) + estC K1 S1 R1 := by
  unfold totB estC
  subst hs hr
  rw [Nat.sub_add_cancel hk1]
  generalize growC = G
  have hq3 : q ^ 3 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hq1 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hqq : q ≤ q ^ 3 := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hq2 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hA : q ^ 3 * (n + 1) ≤ (q + 1) ^ 3 * (n + 1) := Nat.mul_le_mul_right _ hq3
  have hA1 : n + 1 ≤ q ^ 3 * (n + 1) := by nlinarith
  have hA2 : q ^ 3 ≤ q ^ 3 * (n + 1) := by nlinarith
  have hA3 : q ^ 2 * (n + 1) ≤ q ^ 3 * (n + 1) := Nat.mul_le_mul_right _ hq2
  have hA4 : q ^ 2 * m ≤ q ^ 2 * (n + 1) := Nat.mul_le_mul_left _ (by omega)
  rw [show ∀ C : ℕ, C * (q + 1) ^ 3 * (n + 1) = C * ((q + 1) ^ 3 * (n + 1)) from fun C => by ring]
  generalize hP : (q + 1) ^ 3 * (n + 1) = P at hA ⊢
  have eq2 : R1 * q ^ 2 * (1 + ((m * 7 + 3) + (3 + ((8 + G * (S1 * q + 1) * (n + 1)) +
      (1 + ((S1 * q * 19 + 12) + (3 + 0))))))) =
      31 * (R1 * q ^ 2) + 7 * (R1 * (q ^ 2 * m)) + G * R1 * S1 * (q ^ 3 * (n + 1)) +
        G * R1 * (q ^ 2 * (n + 1)) + 19 * (R1 * S1 * q ^ 3) := by ring
  have eq3 : G * k * (n + 1) ≤ G * K1 * P := by
    calc G * k * (n + 1) ≤ G * (K1 * q ^ 3) * (n + 1) := by gcongr
      _ = G * K1 * (q ^ 3 * (n + 1)) := by ring
      _ ≤ G * K1 * P := by gcongr
  have b1 : K1 * q ^ 3 ≤ K1 * P := Nat.mul_le_mul_left _ (by omega)
  have b2 : S1 * q ≤ S1 * P := Nat.mul_le_mul_left _ (by omega)
  have b3 : R1 * q ^ 2 ≤ R1 * P := Nat.mul_le_mul_left _ (by omega)
  have b4 : R1 * (q ^ 2 * m) ≤ R1 * P := Nat.mul_le_mul_left _ (by omega)
  have b5 : G * R1 * S1 * (q ^ 3 * (n + 1)) ≤ G * R1 * S1 * P := Nat.mul_le_mul_left _ (by omega)
  have b6 : G * R1 * (q ^ 2 * (n + 1)) ≤ G * R1 * P := Nat.mul_le_mul_left _ (by omega)
  have b7 : R1 * S1 * q ^ 3 ≤ R1 * S1 * P := Nat.mul_le_mul_left _ (by omega)
  have hn : n ≤ P := by omega
  rw [eq2]
  have : (400 + 5 * K1 + 5 * S1 + 43 * R1 + 19 * (R1 * S1) + 2 * (G * K1) + G * R1 * S1 + G * R1) * P =
      400 * P + 5 * (K1 * P) + 5 * (S1 * P) + 43 * (R1 * P) + 19 * (R1 * S1 * P) + 2 * (G * K1 * P) +
        G * R1 * S1 * P + G * R1 * P := by ring
  rw [this]
  omega

/-- Constant of the query bound. -/
def estQ (K1 S1 R1 : ℕ) : ℕ := 2 * K1 + R1 * (S1 + 1)

lemma query_le (K1 S1 R1 q n k s r : ℕ) (hq : 1 ≤ q) (hk1 : 1 ≤ k) (hkq : k ≤ K1 * q ^ 3)
    (hs : s = S1 * q) (hr : r = R1 * q ^ 2) :
    (k - 1 + 1) * n + (k - 1 + 1) * n + r * ((s + 1) * n) ≤ estQ K1 S1 R1 * (q + 1) ^ 3 * (n + 1) := by
  unfold estQ
  subst hs hr
  rw [Nat.sub_add_cancel hk1]
  have hq3 : q ^ 3 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hq2 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have e : R1 * q ^ 2 * ((S1 * q + 1) * n) = R1 * S1 * (q ^ 3 * n) + R1 * (q ^ 2 * n) := by ring
  have hA : q ^ 3 * n ≤ (q + 1) ^ 3 * (n + 1) := Nat.mul_le_mul hq3 (by omega)
  have hB : q ^ 2 * n ≤ (q + 1) ^ 3 * (n + 1) := le_trans (Nat.mul_le_mul_right _ hq2) hA
  have hk : k * n ≤ K1 * (q ^ 3 * n) := by
    calc k * n ≤ K1 * q ^ 3 * n := Nat.mul_le_mul_right _ hkq
      _ = K1 * (q ^ 3 * n) := by ring
  rw [e, show (2 * K1 + R1 * (S1 + 1)) * (q + 1) ^ 3 * (n + 1) =
    2 * (K1 * ((q + 1) ^ 3 * (n + 1))) + R1 * S1 * ((q + 1) ^ 3 * (n + 1)) +
      R1 * ((q + 1) ^ 3 * (n + 1)) by ring]
  generalize (q + 1) ^ 3 * (n + 1) = P at hA hB ⊢
  have c1 : K1 * (q ^ 3 * n) ≤ K1 * P := Nat.mul_le_mul_left _ hA
  have c2 : R1 * S1 * (q ^ 3 * n) ≤ R1 * S1 * P := Nat.mul_le_mul_left _ hA
  have c3 : R1 * (q ^ 2 * n) ≤ R1 * P := Nat.mul_le_mul_left _ hB
  omega

end MTSPEst

end

section

/-!
# The sublinear MST-weight estimator: program and main theorem

* `MTSPEst.estProg K1 S1 R1 cinv scale` — the program (defined in `Solutions.W.EstCode`);
* spec functions `qOf kOf sOf rOf mOf LOf T0 T1 netP U A' hcap X estOut` (in `Solutions.W.EstSpec`),
  with `hcap` expressed through `MTSPMst.hcap` / `MTSPMst.capF` and the sampled vertices decoded
  with `MTSPDecode.dec`;
* `estProg_adm`, `est_run` below.
-/

open scoped Classical

namespace MTSPEst
open SublinearSteiner SmaleNinth MTSPMst Finset

/-- Step bound: `estC * (q + 1)^3 * (n + 1) + estC`, `q = qOf n`. -/
noncomputable def timeBound (K1 S1 R1 n : ℕ) : ℕ :=
  estC K1 S1 R1 * (qOf n + 1) ^ 3 * (n + 1) + estC K1 S1 R1

/-- Query bound: `(2 K1 + R1 (S1 + 1)) * (q + 1)^3 * (n + 1)`. -/
noncomputable def queryBound (K1 S1 R1 n : ℕ) : ℕ := estQ K1 S1 R1 * (qOf n + 1) ^ 3 * (n + 1)

/-! Admissibility. -/

lemma adm_append {A B : Program} (hA : Admissible A) (hB : Admissible B) : Admissible (A ++ B) := by
  intro i hi
  rcases List.mem_append.mp hi with h | h
  · exact hA i h
  · exact hB i h

lemma adm_nil : Admissible [] := by intro i hi; simp at hi

lemma adm_cons {i : Instr} {P : Program}
    (hi : (∀ d c, i = .core (.const d c) → ∃ q : ℚ, c = (q : ℝ)) ∧ i ≠ .core .accept ∧
      i ≠ .core .reject) (hP : Admissible P) : Admissible (i :: P) := by
  intro j hj
  rcases List.mem_cons.mp hj with rfl | h
  · exact hi
  · exact hP j h

lemma ok_const (d : ℕ) (q : ℚ) :
    (∀ d' c, Instr.core (.const d (q : ℝ)) = .core (.const d' c) → ∃ q' : ℚ, c = (q' : ℝ)) ∧
      Instr.core (.const d (q : ℝ)) ≠ .core .accept ∧ Instr.core (.const d (q : ℝ)) ≠ .core .reject := by
  refine ⟨fun d' c h => ⟨q, ?_⟩, by simp, by simp⟩
  simp only [Instr.core.injEq, RAMInstr.const.injEq] at h
  exact h.2.symm

theorem estProg_adm (K1 S1 R1 : ℕ) (cinv scale : ℚ) : Admissible (estProg K1 S1 R1 cinv scale) := by
  simp only [estProg, pre0, A1code, A2code, A3code, callCode, callArgs, setupCode, qloopCode, paramA,
    countUpCode, paramB, paramC, paramD, mloopCode, layoutCode, t0Code, t1Code, markCode, call2Args,
    apCode, hinitCode, coinCode, testCode, hloopCode, hA, hB, hC, capCode, tailCode, finalCode]
  repeat' first
    | exact MTSPGrow.growCode_adm _ _
    | exact adm_nil
    | apply adm_append
    | (apply adm_cons; first | exact ok_const _ _ | exact ⟨by simp, by simp, by simp⟩)

/-! Main theorem. -/

theorem est_run (K1 S1 R1 : ℕ) (cinv scale : ℚ) (hK1 : 1 ≤ K1) {n : ℕ} (d : Fin n → Fin n → ℝ)
    (hd : DoublingMST.IsMetric d) (f : ℕ → Bool) :
    ∃ T ≤ timeBound K1 S1 R1 n,
      ((step (estProg K1 S1 R1 cinv scale) d f)^[T] (initState (Finset.univ : Finset (Fin n)))).output =
        some (estOut K1 S1 R1 cinv scale d (MTSPDecode.dec (mOf n) f)) ∧
      ((step (estProg K1 S1 R1 cinv scale) d f)^[T] (initState (Finset.univ : Finset (Fin n)))).queries ≤
        queryBound K1 S1 R1 n ∧
      ((step (estProg K1 S1 R1 cinv scale) d f)^[T] (initState (Finset.univ : Finset (Fin n)))).coins ≤
        rOf R1 n * mOf n := by
  have hL := layout K1 S1 R1 cinv scale
  set Q := estProg K1 S1 R1 cinv scale with hQ
  set I := initState (Finset.univ : Finset (Fin n)) with hI
  have hC1 : 400 ≤ estC K1 S1 R1 := by unfold estC; omega
  by_cases hn : n ≤ 1
  · obtain ⟨T, hT, ho, hq, hc⟩ := setup_halt (d := d) (f := f) 0
      (emb_split (X := setupCode 0) hL.pre rfl).1 I rfl rfl rfl init_imem0 hn
    refine ⟨T, by unfold timeBound; omega, ?_, ?_, ?_⟩
    · rw [ho, estOut, dif_pos hn]
    · rw [hq]; exact Nat.zero_le _
    · rw [hc]; exact Nat.zero_le _
  have h0 : 0 < n := by omega
  have hk1 := kOf_pos K1 n hK1 (by omega)
  have hkn := kOf_le K1 n
  have hKL : kOf K1 n - 1 ≤ LOf S1 n := by unfold LOf; omega
  have hLpos : (n : ℤ) ≤ LOf S1 n := by unfold LOf; push_cast; omega
  -- prefix
  obtain ⟨Ta, hTa, hpca, hGa, ha25, ha24, ha23, hia, hca, hqa⟩ :=
    prefix_run (d := d) (f := f) K1 S1 R1 hK1 hL.pre hn
  generalize hSa : (step Q d f)^[Ta] I = Sa at hpca hGa ha25 ha24 ha23 hia hca hqa
  -- first call
  have hmask1 : MTSPGrow.maskOf (n := n) Sa 1 = allOnes := by
    funext u; simp [MTSPGrow.maskOf, allOnes, hia, init_ones u u.isLt]
  obtain ⟨Tb, hTb, hpcb, hGb, hcb, hqb, h108b, hrecb, hkeyb, himb, hppb, hrrb⟩ :=
    call_run (d := d) (f := f) K1 S1 R1 true 63 hL.c1 hd Sa hpca hGa ⟨0, h0⟩ (kOf K1 n - 1) 1
      (by rw [ha25]; rfl) ha24 ha23 hKL (Or.inl rfl)
  rw [hmask1] at h108b hrecb hkeyb
  generalize hSb : (step Q d f)^[Tb] Sa = Sb at hpcb hGb hcb hqb h108b hrecb hkeyb himb hppb hrrb
  set R1r := run1 K1 d h0 with hR1r
  -- pcopy 16 108
  obtain ⟨Tc, hTc, hpcc, hFc, h16c⟩ :=
    pcopy_run (d := d) (f := f) 16 108 b1 hL.a1p Sb (by rw [hpcb]; rfl) hGb.out
  generalize hSc : (step Q d f)^[Tc] Sb = Sc at hpcc hFc h16c
  have hGc := hGb.of_Fr hFc (fun j hj => not_mem_gptrs hj _ (by decide)) (by decide)
  -- T0 scan
  obtain ⟨Td, hTd, hpcd, hFd, h4d⟩ :=
    t0_run (d := d) (f := f) (b1 + 1) hL.t0 Sc hpcc hFc.out (-(LOf S1 n : ℤ))
      (keyN R1r.1) hGc.p1 hGc.p9 (fun u hu => by
        rw [hFc.mem]
        have := hkeyb ⟨u, hu⟩
        simp only [keyN, dif_pos hu]
        exact this)
  generalize hSd : (step Q d f)^[Td] Sc = Sd at hpcd hFd h4d
  have hGd := hGc.of_Fr hFd (fun j hj => not_mem_gptrs hj _ (by decide)) (by decide)
  -- T1
  obtain ⟨Te, hTe, hpce, hFe, h1e⟩ :=
    t1_run (d := d) (f := f) cinv (b1 + 12) hL.t1 Sd (by rw [hpcd]) hFd.out
  generalize hSe : (step Q d f)^[Te] Sd = Se at hpce hFe h1e
  have hGe := hGd.of_Fr hFe (fun j hj => by simp) (by decide)
  have hT1e : Se.cfg.regs 1 = T1 K1 cinv d h0 := by rw [h1e, h4d]; rfl
  -- net mask
  set cnt1 := R1r.2.length with hcnt1
  let vtx : ℕ → ℕ := fun j => if hj : j < cnt1 then ((R1r.2[j]).1 : ℕ) else 0
  have hvtx : ∀ j, vtx j < n := by
    intro j; simp only [vtx]; split_ifs
    · exact Fin.isLt _
    · exact h0
  have h16e : Se.cfg.ptrs 16 = cnt1 := by
    rw [hFe.ptrs 16 (by decide), hFd.ptrs 16 (by decide), h16c, h108b]; rfl
  obtain ⟨Tf, hTf, hpcf, hof, hpf, hrf, hmf, hcf, hqf, hif⟩ :=
    mark_run (d := d) (f := f) (b1 + 14) hL.mark Se (by rw [hpce]) hFe.out
      (-3 * (LOf S1 n : ℤ)) (-2 * (LOf S1 n : ℤ)) cnt1 vtx hGe.p11 hGe.p12 h16e hGe.p10
      (fun j hj => by
        rw [hFe.imem, hFd.imem, hFc.imem, (hrecb j hj).1]
        simp only [vtx, dif_pos hj]; rfl)
      (fun j hj => ⟨by omega, fun j' _ => by have := hvtx j'; omega⟩)
  generalize hSf : (step Q d f)^[Tf] Se = Sf at hpcf hof hpf hrf hmf hcf hqf hif
  have hGf : Glob K1 S1 R1 n Sf := hGe.transfer hof
    (fun j hj => hpf j (not_mem_gptrs hj _ (by decide))) (by rw [hrf])
    (fun u hu => by
      rw [hif]; simp only [markI]
      rw [if_neg]
      rintro (h | ⟨j, -, h⟩)
      · omega
      · have := hvtx j; omega)
  -- arguments of the second call
  obtain ⟨Tg, hTg, hpcg, hFg, h25g, h24g, h23g⟩ :=
    call2args_run (d := d) (f := f) (b1 + 24) hL.c2a Sf (by rw [hpcf]) hof
  generalize hSg : (step Q d f)^[Tg] Sf = Sg at hpcg hFg h25g h24g h23g
  have hGg := hGf.of_Fr hFg (fun j hj => not_mem_gptrs hj _ (by decide)) (by decide)
  have hmask2 : MTSPGrow.maskOf (n := n) Sg (-3 * (LOf S1 n : ℤ)) = netP K1 d h0 := by
    funext u
    have hu := u.isLt
    have hz : Sc.imem (-3 * (LOf S1 n : ℤ) + u) = 0 := by
      rw [hFc.imem, himb _ (by omega) (by omega), hia, init_neg _ (by omega)]
    simp only [MTSPGrow.maskOf, hFg.imem, hif, markI, hFe.imem, hFd.imem, hz, netP]
    congr 1
    apply propext
    constructor
    · intro h
      by_contra hc
      apply h
      rw [if_neg]
      rintro (h1 | ⟨j, hj, h1⟩)
      · exact hc (Or.inl (by omega))
      · apply hc; right
        refine List.mem_map.mpr ⟨R1r.2[j], List.getElem_mem hj, ?_⟩
        apply Fin.ext
        simp only [vtx, dif_pos hj] at h1
        omega
    · intro h
      rw [if_pos]
      · norm_num
      rcases h with h | h
      · left; omega
      · right
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
        exact ⟨j, hj, by simp only [vtx]; rw [dif_pos (show j < cnt1 from hj)]⟩
  -- second call
  obtain ⟨Th, hTh, hpch, hGh, hch, hqh, h108h, hrech, -, -, hpph, hrrh⟩ :=
    call_run (d := d) (f := f) K1 S1 R1 false g2 hL.c2 hd Sg (by rw [hpcg]; rfl) hGg ⟨0, h0⟩
      (kOf K1 n - 1) (-3 * (LOf S1 n : ℤ)) (by rw [h25g]; rfl)
      (by rw [h24g, hGf.p13]) (by rw [h23g, hGf.p11]) hKL (Or.inr rfl)
  rw [hmask2] at h108h hrech
  generalize hSh : (step Q d f)^[Th] Sg = Sh at hpch hGh hch hqh h108h hrech hpph hrrh
  -- pcopy 17 108
  obtain ⟨Ti, hTi, hpci, hFi, h17i⟩ :=
    pcopy_run (d := d) (f := f) 17 108 b2 hL.a2p Sh (by rw [hpch]; rfl) hGh.out
  generalize hSi : (step Q d f)^[Ti] Sh = Si at hpci hFi h17i
  have hGi := hGh.of_Fr hFi (fun j hj => not_mem_gptrs hj _ (by decide)) (by decide)
  have hT1i : Si.cfg.regs 1 = T1 K1 cinv d h0 := by
    rw [hFi.regs 1 (by decide), hrrh 1 (by norm_num), hFg.regs 1 (by decide), hrf, hT1e]
  -- A'
  obtain ⟨Tj, hTj, hpcj, hFj, h2j⟩ :=
    ap_run (d := d) (f := f) (b2 + 1) hL.ap Si hpci hFi.out (-2 * (LOf S1 n : ℤ))
      (run2 K1 d h0).2.length (fun j => (U K1 d h0).getD j 0) (T1 K1 cinv d h0)
      (by rw [h17i, h108h]; rfl) hGi.p10 hT1i
      (fun j hj => by
        rw [hFi.mem, (hrech j hj).2]
        simp only [U, List.getD_eq_getElem?_getD, List.getElem?_map]
        rw [List.getElem?_eq_getElem hj]; rfl)
  generalize hSj : (step Q d f)^[Tj] Si = Sj at hpcj hFj h2j
  have hGj := hGi.of_Fr hFj (fun j hj => not_mem_gptrs hj _ (by decide)) (by decide)
  -- H := 0, i := 0
  obtain ⟨Tk, hTk, hpck, hFk, h3k, h14k⟩ :=
    hinit_run (d := d) (f := f) (b2 + 12) hL.hi Sj (by rw [hpcj]) hFj.out
  generalize hSk : (step Q d f)^[Tk] Sj = Sk at hpck hFk h3k h14k
  have hGk := hGj.of_Fr hFk (fun j hj => not_mem_gptrs hj _ (by decide)) (by decide)
  have hInv0 : OInv K1 S1 R1 cinv d h0 f Sk.queries (A' K1 cinv d h0) 0 Sk := by
    refine ⟨hpck, hGk, ?_, ?_, ?_, h14k, ?_, by simp⟩
    · rw [hFk.regs 1 (by decide), hFj.regs 1 (by decide), hT1i]
    · rw [hFk.regs 2 (by decide), h2j]
      simp only [A', U, List.length_map]
    · rw [h3k]; simp
    · rw [hFk.coins, hFj.coins, hFi.coins, hch, hFg.coins, hcf, hFe.coins, hFd.coins, hFc.coins,
        hcb, hca]; simp
  -- sampling loop and output
  obtain ⟨Tl, hTl, hol, hql, hcl⟩ := reach_loop_exit (Q := Q) (d := d) (f := f)
    (Inv := OInv K1 S1 R1 cinv d h0 f Sk.queries (A' K1 cinv d h0)) (c := iterB S1 n) (e := 1 + 9)
    (P := fun S' => S'.output = some (estOut K1 S1 R1 cinv scale d (MTSPDecode.dec (mOf n) f)) ∧
      S'.queries ≤ Sk.queries + rOf R1 n * ((sOf S1 n + 1) * n) ∧ S'.coins = rOf R1 n * mOf n)
    (rOf R1 n)
    (fun i hi S hS => outer_iter K1 S1 R1 cinv scale hL hd h0 f _ _ i hi S hS)
    (fun S hS => by
      obtain ⟨hpc, hG, h1, h2, h3, h14, hc, hq⟩ := hS
      refine reach_bind (head_exit (b3 + 35) (b2 + 14) hL.hd S hpc hG.out (rOf R1 n) hG.p5 h14) ?_
      rintro S1' ⟨hpc1, hF1⟩
      refine reach_mono (le_refl _) ?_ (final_run scale (b3 + 35) hL.fin S1' hpc1 hF1.out (mOf n)
        (rOf R1 n) ((hF1.ptrs 7 (by decide)).trans hG.p7) ((hF1.ptrs 5 (by decide)).trans hG.p5))
      rintro S2 ⟨ho2, hq2, hc2⟩
      refine ⟨?_, by rw [hq2, hF1.queries]; exact hq, by rw [hc2, hF1.coins, hc]⟩
      rw [ho2, hF1.regs 1 (by decide), hF1.regs 2 (by decide), hF1.regs 3 (by decide), h1, h2, h3,
        estOut, dif_neg hn])
    Sk hInv0
  generalize hSl : (step Q d f)^[Tl] Sk = Sl at hol hql hcl
  have c := iter_trans hSa hSb
  have c := iter_trans c hSc
  have c := iter_trans c hSd
  have c := iter_trans c hSe
  have c := iter_trans c hSf
  have c := iter_trans c hSg
  have c := iter_trans c hSh
  have c := iter_trans c hSi
  have c := iter_trans c hSj
  have c := iter_trans c hSk
  have c := iter_trans c hSl
  refine ⟨_, ?_, by rw [c]; exact hol, ?_, by rw [c, hcl]⟩
  · have hc1 : cnt1 ≤ kOf K1 n := by
      have := grun_len_le d true allOnes ⟨0, h0⟩ (kOf K1 n - 1); simp only [hcnt1, hR1r, run1]; omega
    have hc2 : (run2 K1 d h0).2.length ≤ kOf K1 n := by
      have := grun_len_le d false (netP K1 d h0) ⟨0, h0⟩ (kOf K1 n - 1); simp only [run2]; omega
    have hB := time_le K1 S1 R1 (qOf n) n (kOf K1 n) (sOf S1 n) (rOf R1 n) (mOf n) cnt1
      (run2 K1 d h0).2.length (qOf_pos n) hk1 hkn (min_le_right _ _) rfl rfl (mOf_le n) hc1 hc2
    unfold timeBound
    refine le_trans ?_ hB
    unfold totB iterB contB at *
    unfold preB at hTa
    omega
  · rw [c]
    have hq := query_le K1 S1 R1 (qOf n) n (kOf K1 n) (sOf S1 n) (rOf R1 n) (qOf_pos n) hk1
      (min_le_right _ _) rfl rfl
    have e1 : Sk.queries = Sh.queries := by rw [hFk.queries, hFj.queries, hFi.queries]
    have e2 : Sg.queries = Sb.queries := by
      rw [hFg.queries, hqf, hFe.queries, hFd.queries, hFc.queries]
    unfold queryBound
    omega

end MTSPEst

end

section

/-!
Basic invariants of the greedy growth `grun` (any mode, any mask).
-/

open scoped Classical

namespace MTSPMst
open Finset

variable {n : ℕ}

section Basic
variable (d : Fin n → Fin n → ℝ) (mode : Bool) (mask : Fin n → Bool) (start : Fin n)

lemma mem_cands {g : GState n} {u : Fin n} : u ∈ cands mask g ↔ mask u = true ∧ u ∉ g.S := by
  simp [cands]

lemma pick_spec {g : GState n} (h : (cands mask g).Nonempty) :
    pick mode mask g h ∈ cands mask g ∧ g.key (pick mode mask g h) = bestKey mode mask g h :=
  Finset.mem_filter.mp (Finset.min'_mem _ (bestKey_mem mode mask g h))

lemma bestKey_false_le {g : GState n} (h : (cands mask g).Nonempty) {c : Fin n}
    (hc : c ∈ cands mask g) : bestKey false mask g h ≤ g.key c := by
  rw [bestKey, if_neg Bool.false_ne_true]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hc)

lemma le_bestKey_true {g : GState n} (h : (cands mask g).Nonempty) {c : Fin n}
    (hc : c ∈ cands mask g) : g.key c ≤ bestKey true mask g h := by
  rw [bestKey, if_pos rfl]
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ hc)

lemma grun_zero : grun d mode mask start 0 = (ginit d start, []) := rfl

lemma grun_succ_pos (j : ℕ) (h : (cands mask (grun d mode mask start j).1).Nonempty) :
    grun d mode mask start (j + 1) =
      (⟨insert (pick mode mask _ h) (grun d mode mask start j).1.S,
        fun x => min ((grun d mode mask start j).1.key x) (d x (pick mode mask _ h))⟩,
       (grun d mode mask start j).2 ++
        [(pick mode mask _ h, (grun d mode mask start j).1.key (pick mode mask _ h))]) := by
  simp only [grun, gstep, dif_pos h]

lemma grun_succ_neg (j : ℕ) (h : ¬ (cands mask (grun d mode mask start j).1).Nonempty) :
    grun d mode mask start (j + 1) = grun d mode mask start j := by
  simp only [grun, gstep, dif_neg h]

/-- The general invariant of the greedy growth. -/
structure Inv (g : GState n) (L : List (Fin n × ℝ)) : Prop where
  hS : g.S = insert start (L.map Prod.fst).toFinset
  hnd : (L.map Prod.fst).Nodup
  hmem : ∀ p ∈ L, mask p.1 = true ∧ p.1 ≠ start
  hle : ∀ x, ∀ p ∈ g.S, g.key x ≤ d x p
  hex : ∀ x, ∃ p ∈ g.S, g.key x = d x p

lemma inv_grun (j : ℕ) :
    Inv d mask start (grun d mode mask start j).1 (grun d mode mask start j).2 := by
  induction j with
  | zero =>
    refine ⟨by simp [grun_zero, ginit], by simp [grun_zero], by simp [grun_zero], ?_, ?_⟩
    · intro x p hp
      simp only [grun_zero, ginit, Finset.mem_singleton] at hp ⊢
      rw [hp]
    · intro x
      exact ⟨start, by simp [grun_zero, ginit], by simp [grun_zero, ginit]⟩
  | succ j ih =>
    by_cases h : (cands mask (grun d mode mask start j).1).Nonempty
    · rw [grun_succ_pos d mode mask start j h]
      set g := (grun d mode mask start j).1
      set L := (grun d mode mask start j).2
      set u := pick mode mask g h
      obtain ⟨hu, -⟩ := pick_spec mode mask h
      rw [mem_cands] at hu
      have huL : u ∉ L.map Prod.fst := by
        intro hm
        apply hu.2
        rw [ih.hS]
        exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr hm)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only
        rw [ih.hS]
        ext x
        simp only [Finset.mem_insert, List.mem_toFinset, List.map_append, List.mem_append,
          List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
        tauto
      · simp only [List.map_append, List.map_cons, List.map_nil]
        rw [List.nodup_append]
        refine ⟨ih.hnd, List.nodup_singleton _, ?_⟩
        intro a ha b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb
        rintro rfl
        exact huL ha
      · intro p hp
        rw [List.mem_append] at hp
        rcases hp with hp | hp
        · exact ih.hmem p hp
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          subst hp
          refine ⟨hu.1, ?_⟩
          intro hus
          have hus' : pick mode mask g h = start := hus
          apply hu.2
          rw [ih.hS, hus']
          exact Finset.mem_insert_self _ _
      · intro x p hp
        simp only [Finset.mem_insert] at hp ⊢
        rcases hp with rfl | hp
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (ih.hle x p hp)
      · intro x
        simp only
        rcases le_total (g.key x) (d x u) with hle | hle
        · obtain ⟨p, hp, hpx⟩ := ih.hex x
          exact ⟨p, Finset.mem_insert_of_mem hp, by rw [min_eq_left hle, hpx]⟩
        · exact ⟨u, Finset.mem_insert_self _ _, by rw [min_eq_right hle]⟩
    · rw [grun_succ_neg d mode mask start j h]
      exact ih

lemma Inv.card_S {g : GState n} {L : List (Fin n × ℝ)} (I : Inv d mask start g L) :
    g.S.card = L.length + 1 := by
  rw [I.hS, Finset.card_insert_of_notMem, List.toFinset_card_of_nodup I.hnd, List.length_map]
  rw [List.mem_toFinset, List.mem_map]
  rintro ⟨p, hp, hps⟩
  exact (I.hmem p hp).2 hps

lemma Inv.S_sub {g : GState n} {L : List (Fin n × ℝ)} (I : Inv d mask start g L)
    (hs : mask start = true) : g.S ⊆ univ.filter (fun u => mask u = true) := by
  intro x hx
  rw [I.hS, Finset.mem_insert, List.mem_toFinset, List.mem_map] at hx
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases hx with rfl | ⟨p, hp, rfl⟩
  · exact hs
  · exact (I.hmem p hp).1

lemma Inv.start_mem {g : GState n} {L : List (Fin n × ℝ)} (I : Inv d mask start g L) :
    start ∈ g.S := by
  rw [I.hS]; exact Finset.mem_insert_self _ _

lemma grun_length (hs : mask start = true) (j : ℕ) :
    (grun d mode mask start j).2.length = min j ((univ.filter (fun u => mask u = true)).card - 1) := by
  induction j with
  | zero => simp [grun_zero]
  | succ j ih =>
    have I := inv_grun d mode mask start j
    have hc := I.card_S
    have hsub := Inv.S_sub d mask start I hs
    by_cases h : (cands mask (grun d mode mask start j).1).Nonempty
    · rw [grun_succ_pos d mode mask start j h]
      simp only [List.length_append, List.length_cons, List.length_nil]
      obtain ⟨hu, -⟩ := pick_spec mode mask h
      rw [mem_cands] at hu
      have hlt : (grun d mode mask start j).1.S.card < (univ.filter (fun u => mask u = true)).card := by
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
        intro heq
        apply hu.2
        rw [heq, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hu.1⟩
      omega
    · rw [grun_succ_neg d mode mask start j h]
      have heq : (grun d mode mask start j).1.S = univ.filter (fun u => mask u = true) := by
        apply Finset.Subset.antisymm hsub
        intro x hx
        by_contra hxS
        apply h
        refine ⟨x, ?_⟩
        rw [mem_cands]
        exact ⟨(Finset.mem_filter.mp hx).2, hxS⟩
      rw [heq] at hc
      omega

lemma grun_prefix {j s : ℕ} (h : j ≤ s) :
    (grun d mode mask start j).2 <+: (grun d mode mask start s).2 := by
  induction s, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ s _ ih =>
    by_cases h : (cands mask (grun d mode mask start s).1).Nonempty
    · rw [grun_succ_pos d mode mask start s h]
      exact ih.trans (List.prefix_append _ _)
    · rw [grun_succ_neg d mode mask start s h]
      exact ih

end Basic

end MTSPMst

end

section

/-!
Prim (mode = false): threshold invariants, component counting and the prefix property.
-/

open scoped Classical

namespace MTSPMst
open Finset

variable {n : ℕ}

section Prim
variable (d : Fin n → Fin n → ℝ) (mask : Fin n → Bool) (start : Fin n)

lemma thr_adj_iff {Q : Finset (Fin n)} {t : ℝ} {a b : Fin n} :
    (thrGraph d Q t).Adj a b ↔ a ≠ b ∧ ((a ∈ Q ∧ b ∈ Q ∧ d a b ≤ t) ∨ (b ∈ Q ∧ a ∈ Q ∧ d b a ≤ t)) := by
  unfold thrGraph
  rw [SimpleGraph.fromRel_adj]

/-- If Prim's recorded value exceeds `t`, the selected set is closed in the threshold graph. -/
lemma prim_closed (hd : DoublingMST.IsMetric d) {Q : Finset (Fin n)}
    (hmask : ∀ u, mask u = true ↔ u ∈ Q) {t : ℝ} {g : GState n}
    (hle : ∀ x, ∀ p ∈ g.S, g.key x ≤ d x p) (h : (cands mask g).Nonempty)
    (ht : t < g.key (pick false mask g h)) {a b : Fin n} (ha : a ∈ g.S)
    (hab : (thrGraph d Q t).Reachable a b) : b ∈ g.S := by
  have step : ∀ x y, x ∈ g.S → (thrGraph d Q t).Adj x y → y ∈ g.S := by
    intro x y hx hxy
    by_contra hy
    rw [thr_adj_iff] at hxy
    obtain ⟨-, hr⟩ := hxy
    have hyQ : y ∈ Q := by rcases hr with h1 | h1 <;> tauto
    have hdy : d y x ≤ t := by
      rcases hr with h1 | h1
      · rw [hd.2.1]; exact h1.2.2
      · exact h1.2.2
    have hyc : y ∈ cands mask g := (mem_cands mask).mpr ⟨(hmask y).mpr hyQ, hy⟩
    have h1 := bestKey_false_le mask h hyc
    have h2 := (pick_spec false mask h).2
    have h3 := hle y x hx
    linarith
  obtain ⟨w⟩ := hab
  revert ha
  induction w with
  | nil => exact id
  | cons hadj w ih => intro hx; exact ih (step _ _ hx hadj)

/-- If Prim's recorded value is at most `t`, the picked point is adjacent to the selected set. -/
lemma prim_adj {Q : Finset (Fin n)} (hmask : ∀ u, mask u = true ↔ u ∈ Q) {t : ℝ} {g : GState n}
    (hSQ : g.S ⊆ Q) (hex : ∀ x, ∃ p ∈ g.S, g.key x = d x p) (h : (cands mask g).Nonempty)
    (ht : g.key (pick false mask g h) ≤ t) :
    ∃ p ∈ g.S, (thrGraph d Q t).Adj (pick false mask g h) p := by
  obtain ⟨hu, -⟩ := pick_spec false mask h
  rw [mem_cands] at hu
  obtain ⟨p, hp, hpk⟩ := hex (pick false mask g h)
  refine ⟨p, hp, ?_⟩
  rw [thr_adj_iff]
  refine ⟨?_, Or.inl ⟨(hmask _).mp hu.1, hSQ hp, hpk ▸ ht⟩⟩
  rintro rfl
  exact hu.2 hp

lemma S_sub_Q {Q : Finset (Fin n)} (hmask : ∀ u, mask u = true ↔ u ∈ Q) (hs : start ∈ Q)
    {g : GState n} {L : List (Fin n × ℝ)} (I : Inv d mask start g L) : g.S ⊆ Q := by
  intro x hx
  have := Inv.S_sub d mask start I ((hmask start).mpr hs) hx
  exact (hmask x).mp (Finset.mem_filter.mp this).2

/-- Component counting invariant. -/
lemma prim_count_inv (hd : DoublingMST.IsMetric d) {Q : Finset (Fin n)}
    (hmask : ∀ u, mask u = true ↔ u ∈ Q) (hs : start ∈ Q) (t : ℝ) (j : ℕ) :
    ((grun d false mask start j).1.S.image (thrGraph d Q t).connectedComponentMk).card
      = ((grun d false mask start j).2.filter (fun p => decide (t < p.2))).length + 1 := by
  induction j with
  | zero => simp [grun_zero, ginit]
  | succ j ih =>
    have I := inv_grun d false mask start j
    by_cases h : (cands mask (grun d false mask start j).1).Nonempty
    · rw [grun_succ_pos d false mask start j h]
      simp only
      set g := (grun d false mask start j).1 with hg
      set L := (grun d false mask start j).2 with hL
      set u := pick false mask g h with hu_def
      obtain ⟨hu, -⟩ := pick_spec false mask h
      rw [mem_cands] at hu
      rw [Finset.image_insert, List.filter_append, List.length_append]
      by_cases hk : t < g.key u
      · have hnot : (thrGraph d Q t).connectedComponentMk u ∉
            g.S.image (thrGraph d Q t).connectedComponentMk := by
          rw [Finset.mem_image]
          rintro ⟨p, hp, hpu⟩
          rw [SimpleGraph.ConnectedComponent.eq] at hpu
          exact hu.2 (prim_closed d mask hd hmask I.hle h hk hp hpu)
        rw [Finset.card_insert_of_notMem hnot, ih]
        have hk' : t < (grun d false mask start j).1.key u := hk
        simp [hk']
      · have hin : (thrGraph d Q t).connectedComponentMk u ∈
            g.S.image (thrGraph d Q t).connectedComponentMk := by
          obtain ⟨p, hp, hadj⟩ := prim_adj d mask hmask (S_sub_Q d mask start hmask hs I) I.hex h
            (le_of_not_gt hk)
          rw [Finset.mem_image]
          exact ⟨p, hp, SimpleGraph.ConnectedComponent.eq.mpr hadj.reachable.symm⟩
        rw [Finset.insert_eq_of_mem hin, ih]
        have hk' : ¬ t < (grun d false mask start j).1.key u := hk
        simp [hk']
    · rw [grun_succ_neg d false mask start j h]
      exact ih

end Prim

/-- **(a)** Prim on `Q`, started in `Q`, run to exhaustion: the recorded values `> t` count the
threshold components minus one. -/
theorem prim_count (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (Q : Finset (Fin n))
    (start : Fin n) (hs : start ∈ Q) (t : ℝ) (_ht : 0 ≤ t) :
    ((grun d false (fun u => decide (u ∈ Q)) start (Q.card - 1)).2.filter
        (fun p => decide (t < p.2))).length + 1 = compCount d Q t := by
  have hmask : ∀ u, (fun u => decide (u ∈ Q)) u = true ↔ u ∈ Q := by simp
  rw [← prim_count_inv d _ start hd hmask hs t]
  have I := inv_grun d false (fun u => decide (u ∈ Q)) start (Q.card - 1)
  have hlen := grun_length d false (fun u => decide (u ∈ Q)) start (by simpa using hs) (Q.card - 1)
  have hM : (univ.filter (fun u => (fun u => decide (u ∈ Q)) u = true)).card = Q.card := by
    congr 1; ext x; simp
  rw [hM] at hlen
  have hc := Inv.card_S _ _ _ I
  have hQpos : 0 < Q.card := Finset.card_pos.mpr ⟨start, hs⟩
  have hSQ := S_sub_Q d _ start hmask hs I
  have hSeq : (grun d false (fun u => decide (u ∈ Q)) start (Q.card - 1)).1.S = Q :=
    Finset.eq_of_subset_of_card_le hSQ (by omega)
  rw [hSeq]
  rfl

lemma foldl_max_le_iff (t : ℝ) : ∀ (l : List ℝ) (a : ℝ),
    l.foldl max a ≤ t ↔ a ≤ t ∧ ∀ x ∈ l, x ≤ t
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_max_le_iff t l, max_le_iff]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

/-- Length of Prim's record list on all points. -/
theorem prim_length (d : Fin n → Fin n → ℝ) (v : Fin n) (s : ℕ) :
    ((grun d false (fun _ => true) v s).2).length = min s (n - 1) := by
  rw [grun_length d false (fun _ => true) v rfl s]
  simp

lemma prefix_inv (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (v : Fin n) (t : ℝ)
    (j : ℕ) :
    ((∀ x ∈ (grun d false (fun _ => true) v j).2, x.2 ≤ t) →
      ∀ p ∈ (grun d false (fun _ => true) v j).1.S, (thrGraph d univ t).Reachable v p) ∧
    ((∃ x ∈ (grun d false (fun _ => true) v j).2, t < x.2) →
      univ.filter (fun u => (thrGraph d univ t).Reachable v u) ⊂
        (grun d false (fun _ => true) v j).1.S) := by
  have hmask : ∀ u, (fun _ => true) u = true ↔ u ∈ (univ : Finset (Fin n)) := by simp
  induction j with
  | zero =>
    refine ⟨?_, by simp [grun_zero]⟩
    intro _ p hp
    simp only [grun_zero, ginit, Finset.mem_singleton] at hp
    rw [hp]
  | succ j ih =>
    have I := inv_grun d false (fun _ => true) v j
    by_cases h : (cands (fun _ => true) (grun d false (fun _ => true) v j).1).Nonempty
    · rw [grun_succ_pos d false _ v j h]
      simp only
      set g := (grun d false (fun _ => true) v j).1 with hg
      set L := (grun d false (fun _ => true) v j).2 with hL
      set u := pick false (fun _ => true) g h with hu_def
      obtain ⟨hu, -⟩ := pick_spec false (fun _ => true) h
      rw [mem_cands] at hu
      refine ⟨?_, ?_⟩
      · intro hall p hp
        have hallL : ∀ x ∈ L, x.2 ≤ t := fun x hx => hall x (List.mem_append_left _ hx)
        have hk : g.key u ≤ t := hall _ (List.mem_append_right _ (List.mem_singleton_self _))
        rw [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · obtain ⟨q, hq, hadj⟩ := prim_adj d _ hmask (Finset.subset_univ _) I.hex h hk
          exact (ih.1 hallL q hq).trans hadj.reachable.symm
        · exact ih.1 hallL p hp
      · rintro ⟨x, hx, hxt⟩
        by_cases hex : ∃ y ∈ L, t < y.2
        · exact Finset.ssubset_of_ssubset_of_subset (ih.2 hex) (Finset.subset_insert _ _)
        · rw [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact absurd ⟨x, hx, hxt⟩ hex
          · refine Finset.ssubset_of_subset_of_ssubset ?_ (Finset.ssubset_insert hu.2)
            intro w hw
            rw [Finset.mem_filter] at hw
            exact prim_closed d _ hd hmask I.hle h hxt (Inv.start_mem d _ v I) hw.2
    · rw [grun_succ_neg d false _ v j h]
      exact ih

/-- **(b)** Prefix property of Prim from `v` on all points. -/
theorem prim_prefix (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (v : Fin n) (s : ℕ)
    (t : ℝ) (ht : 0 ≤ t) (j : ℕ) (hj : j ≤ s) (hjn : j < n) :
    j + 1 ≤ compSize d Finset.univ t v ↔
      pmax ((grun d false (fun _ => true) v s).2.map Prod.snd) j ≤ t := by
  have hlenj := prim_length d v j
  rw [min_eq_left (by omega)] at hlenj
  have hpre := grun_prefix d false (fun _ => true) v hj
  have htake : ((grun d false (fun _ => true) v s).2.map Prod.snd).take j
      = (grun d false (fun _ => true) v j).2.map Prod.snd := by
    rw [← List.map_take]
    congr 1
    conv_rhs => rw [List.prefix_iff_eq_take.mp hpre, hlenj]
  unfold pmax
  rw [htake, foldl_max_le_iff]
  have I := inv_grun d false (fun _ => true) v j
  have hc := Inv.card_S _ _ _ I
  rw [hlenj] at hc
  have hinv := prefix_inv d hd v t j
  unfold compSize
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro hle
    refine ⟨ht, ?_⟩
    by_contra hne
    push Not at hne
    have := Finset.card_lt_card (hinv.2 hne)
    omega
  · rintro ⟨-, hall⟩
    rw [← hc]
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hinv.1 hall p hp⟩

end MTSPMst

end

section

namespace MTSPBridge
open Finset CombOpt.SpanningTree

variable {n : ℕ}

lemma isMetricCost_of_isMetric {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) :
    MetricTSP.IsMetricCost d :=
  ⟨hd.2.1, fun v => (hd.1 v v).2 rfl, fun u v w => hd.2.2 u v w⟩

lemma dist_nonneg' {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (u v : Fin n) :
    0 ≤ d u v := by
  have h := hd.2.2 u v u
  rw [(hd.1 u u).2 rfl, hd.2.1 v u] at h
  linarith

lemma edgeCost_mk {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (u v : Fin n) :
    DoublingMST.edgeCost d s(u, v) = d u v := by
  show min (d u v) (d v u) = d u v
  rw [hd.2.1 v u, min_self]

lemma edgeCost_nonneg {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (e : Sym2 (Fin n)) :
    0 ≤ DoublingMST.edgeCost d e := by
  induction e with
  | _ u v => rw [edgeCost_mk hd]; exact dist_nonneg' hd u v

lemma edgeCost_diag {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (a : Fin n) :
    DoublingMST.edgeCost d s(a, a) = 0 := by
  rw [edgeCost_mk hd]; exact (hd.1 a a).2 rfl

lemma pairCost_eq_edgeCost {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (e : Sym2 (Fin n)) :
    MetricTSP.pairCost d e = DoublingMST.edgeCost d e := by
  induction e with
  | _ u v =>
    rw [edgeCost_mk hd]
    show (d u v + d v u) / 2 = d u v
    rw [hd.2.1 v u]; ring

/-! ### Walks -/

/-- A Mathlib walk as a walk of the complete graph. -/
noncomputable def ofWalk {G : SimpleGraph (Fin n)} :
    {u v : Fin n} → G.Walk u v → (DoublingMST.completeGraph n).Walk u v
  | _, _, SimpleGraph.Walk.nil => Graph.Walk.nil _
  | u, _, SimpleGraph.Walk.cons (v := w) _ p => Graph.Walk.cons s(u, w) rfl (ofWalk p)

lemma ofWalk_edges {G : SimpleGraph (Fin n)} {u v : Fin n} (p : G.Walk u v) :
    (ofWalk p).edges = p.edges := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [ofWalk, Graph.Walk.edges, SimpleGraph.Walk.edges_cons, ih]

/-- A walk of the complete graph whose edges are edges of `G`, as a Mathlib walk of `G`. -/
noncomputable def toWalk (G : SimpleGraph (Fin n)) :
    {u v : Fin n} → (p : (DoublingMST.completeGraph n).Walk u v) →
      (∀ e ∈ p.edges, e ∈ G.edgeSet) → G.Walk u v
  | _, _, Graph.Walk.nil _, _ => SimpleGraph.Walk.nil
  | _, _, Graph.Walk.cons e h p, hp =>
      SimpleGraph.Walk.cons
        (by
          have he : e ∈ G.edgeSet := hp e (by simp [Graph.Walk.edges])
          have h' : e = _ := h
          rw [h'] at he
          exact (SimpleGraph.mem_edgeSet G).mp he)
        (toWalk G p (fun e' he' => hp e' (by simp [Graph.Walk.edges, he'])))

lemma toWalk_edges (G : SimpleGraph (Fin n)) {u v : Fin n}
    (p : (DoublingMST.completeGraph n).Walk u v) (hp : ∀ e ∈ p.edges, e ∈ G.edgeSet) :
    (toWalk G p hp).edges = p.edges := by
  induction p with
  | nil => rfl
  | cons e h p ih =>
    have h' : e = _ := h
    rw [toWalk, SimpleGraph.Walk.edges_cons, Graph.Walk.edges, ih, h']

lemma toWalk_support (G : SimpleGraph (Fin n)) {u v : Fin n}
    (p : (DoublingMST.completeGraph n).Walk u v) (hp : ∀ e ∈ p.edges, e ∈ G.edgeSet) :
    (toWalk G p hp).support = p.support := by
  induction p with
  | nil => rfl
  | cons e h p ih =>
    rw [toWalk, SimpleGraph.Walk.support_cons, Graph.Walk.support, ih]

lemma tail_nodup_of_dropLast_nodup {α : Type*} (v : α) (t : List α) (ht : t ≠ [])
    (hlast : t.getLast ht = v) (h : (v :: t).dropLast.Nodup) : t.Nodup := by
  rw [List.dropLast_cons_of_ne_nil ht] at h
  have ht' : t = t.dropLast ++ [v] := by
    conv_lhs => rw [← List.dropLast_append_getLast ht]
    rw [hlast]
  rw [ht']
  exact (List.perm_append_singleton v t.dropLast).nodup_iff.mpr h

open Classical in
/-- The edges of a Mathlib tree form a spanning tree of the complete graph. -/
theorem isSpanningTree_of_isTree (G : SimpleGraph (Fin n)) (hG : G.IsTree) :
    (DoublingMST.completeGraph n).IsSpanningTree G.edgeSet.toFinset := by
  classical
  constructor
  · intro u v
    obtain ⟨p⟩ := hG.connected.preconnected u v
    refine ⟨ofWalk p, ?_⟩
    intro e he
    rw [ofWalk_edges] at he
    rw [Set.mem_toFinset]
    exact p.edges_subset_edgeSet he
  · rintro ⟨v, p, hcirc, hsub⟩
    have hp : ∀ e ∈ p.edges, e ∈ G.edgeSet := fun e he => by
      have := hsub e he
      rwa [Set.mem_toFinset] at this
    obtain ⟨q, hqe, hqs⟩ : ∃ q : G.Walk v v, q.edges = p.edges ∧ q.support = p.support :=
      ⟨toWalk G p hp, toWalk_edges G p hp, toWalk_support G p hp⟩
    apply hG.isAcyclic q
    rw [SimpleGraph.Walk.isCycle_def]
    obtain ⟨hnd, hdl, hlen⟩ := hcirc
    have hlen' : 1 ≤ q.length := by rw [← SimpleGraph.Walk.length_edges, hqe]; exact hlen
    have hne : q ≠ SimpleGraph.Walk.nil := by
      intro h
      rw [h] at hlen'
      simp at hlen'
    refine ⟨?_, hne, ?_⟩
    · rw [SimpleGraph.Walk.isTrail_def, hqe]; exact hnd
    · have hsupp : q.support = v :: q.support.tail := (q.cons_tail_support).symm
      have htne : q.support.tail ≠ [] := by
        intro h
        have hl := q.length_support
        rw [hsupp, h] at hl
        simp only [List.length_cons, List.length_nil] at hl
        omega
      have hgl : ∀ (L : List (Fin n)) (hL : L ≠ []) (ht : L.tail ≠ []),
          L.getLast hL = L.tail.getLast ht := by
        intro L hL ht
        cases L with
        | nil => exact absurd rfl hL
        | cons a t => exact List.getLast_cons ht
      apply tail_nodup_of_dropLast_nodup v q.support.tail htne
      · rw [← hgl q.support (by simp) htne]
        exact q.getLast_support
      · rw [← hsupp, hqs]; exact hdl

/-- A forest contains no loop. -/
lemma not_isDiag_of_isForest {T : Finset (Sym2 (Fin n))}
    (hT : (DoublingMST.completeGraph n).IsForest T) {e : Sym2 (Fin n)} (he : e ∈ T) :
    ¬ e.IsDiag := by
  intro hdiag
  induction e with
  | _ a b =>
    rw [Sym2.mk_isDiag_iff] at hdiag
    subst hdiag
    apply hT
    refine ⟨a, Graph.Walk.cons s(a, a) rfl (Graph.Walk.nil a), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simp [Graph.Walk.edges]
      · simp [Graph.Walk.support]
      · simp [Graph.Walk.edges]
    · intro e he
      simp [Graph.Walk.edges] at he
      rw [he]; exact he ▸ ‹s(a, a) ∈ T›

/-- A walk from inside `A` to outside `A` uses an edge of the cut `δ(A)`. -/
lemma walk_crosses (A : Finset (Fin n)) {u v : Fin n} (p : (DoublingMST.completeGraph n).Walk u v)
    (hu : u ∈ A) (hv : v ∉ A) : ∃ e ∈ p.edges, e ∈ MetricTSPSublinear.cutEdges univ A := by
  classical
  induction p with
  | nil => exact absurd hu hv
  | @cons a b c e h p ih =>
    by_cases hb : b ∈ A
    · obtain ⟨e', he', hcut⟩ := ih hb hv
      exact ⟨e', by simp [Graph.Walk.edges, he'], hcut⟩
    · refine ⟨e, by simp [Graph.Walk.edges], ?_⟩
      have h' : e = s(a, b) := h
      rw [h']
      unfold MetricTSPSublinear.cutEdges
      exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨hu, by simp [hb]⟩, rfl⟩

/-- The cut sum over unordered pairs as a double sum over ordered pairs. -/
lemma cut_sum (A : Finset (Fin n)) (x : Sym2 (Fin n) → ℝ) :
    ∑ e ∈ MetricTSPSublinear.cutEdges univ A, x e = ∑ u ∈ A, ∑ v ∈ Aᶜ, x s(u, v) := by
  classical
  unfold MetricTSPSublinear.cutEdges
  rw [Finset.sum_image]
  · rw [Finset.compl_eq_univ_sdiff, Finset.sum_product]
  · rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_sdiff,
      Finset.mem_univ, true_and] at hab hab'
    simp only at heq
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · exfalso; rw [h1] at hab; exact hab'.2 hab.1

/-- Double sum over ordered pairs versus sum over unordered non-diagonal pairs. -/
lemma double_sum_sym2 (g : Sym2 (Fin n) → ℝ) (hg : ∀ a, g s(a, a) = 0) :
    ∑ u, ∑ v, g s(u, v) = 2 * ∑ e ∈ MetricTSPSublinear.pairsIn (univ : Finset (Fin n)), g e := by
  classical
  unfold MetricTSPSublinear.pairsIn
  rw [Finset.sum_sym2_filter_not_isDiag]
  rw [← Finset.sum_product']
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ ×ˢ univ : Finset (Fin n × Fin n))
    (fun p => p.1 < p.2) (fun p => g s(p.1, p.2))
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    ((univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => ¬ p.1 < p.2))
    (fun p => p.2 < p.1) (fun p => g s(p.1, p.2))
  have hdiag0 : ∑ p ∈ ((univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => ¬ p.1 < p.2)).filter
      (fun p => ¬ p.2 < p.1), g s(p.1, p.2) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp only [Finset.mem_filter] at hp
    have : p.1 = p.2 := le_antisymm (not_lt.mp hp.2) (not_lt.mp hp.1.2)
    rw [this, hg]
  have hswap : ∑ p ∈ ((univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => ¬ p.1 < p.2)).filter
      (fun p => p.2 < p.1), g s(p.1, p.2)
      = ∑ p ∈ (univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2), g s(p.1, p.2) := by
    apply Finset.sum_nbij' Prod.swap Prod.swap
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp ⊢
      exact hp.2
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp ⊢
      exact ⟨not_lt.mpr (le_of_lt hp), hp⟩
    · intro p _; rfl
    · intro p _; rfl
    · intro p _; simp [Sym2.eq_swap]
  have hoff : (univ : Finset (Fin n)).offDiag.filter (fun i => i.1 < i.2)
      = (univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product, Finset.mem_univ,
      true_and]
    exact ⟨fun h => h.2, fun h => ⟨ne_of_lt h, h⟩⟩
  rw [hoff, ← hsplit, ← hsplit2, hdiag0, hswap]
  ring

end MTSPBridge

end

section

namespace MTSPBridge
open Finset CombOpt.SpanningTree

variable {n : ℕ}

/-- The complete graph has a spanning tree. -/
lemma exists_spanningTree (n : ℕ) :
    ∃ T : Finset (Sym2 (Fin n)), (DoublingMST.completeGraph n).IsSpanningTree T := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨∅, ?_, ?_⟩
    · intro u; exact u.elim0
    · rintro ⟨v, _⟩; exact v.elim0
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨TT, _, hTT⟩ := (SimpleGraph.connected_top : (⊤ : SimpleGraph (Fin n)).Connected).exists_isTree_le
    exact ⟨_, isSpanningTree_of_isTree TT hTT⟩

/-- An MST exists and realizes `mstWeight`. -/
lemma exists_mst (d : Fin n → Fin n → ℝ) :
    ∃ E : Finset (Sym2 (Fin n)), (DoublingMST.completeGraph n).IsSpanningTree E ∧
      DoublingMST.treeWeight d E = DoublingMST.mstWeight d ∧
      ∀ T, (DoublingMST.completeGraph n).IsSpanningTree T →
        DoublingMST.treeWeight d E ≤ DoublingMST.treeWeight d T := by
  classical
  set S := (univ : Finset (Finset (Sym2 (Fin n)))).filter
    (fun T => (DoublingMST.completeGraph n).IsSpanningTree T) with hS
  obtain ⟨T0, hT0⟩ := exists_spanningTree n
  have hSne : S.Nonempty := ⟨T0, by simp [hS, hT0]⟩
  obtain ⟨E, hE, hmin⟩ := Finset.exists_min_image S (DoublingMST.treeWeight d) hSne
  have hEsp : (DoublingMST.completeGraph n).IsSpanningTree E := by simpa [hS] using hE
  have hmin' : ∀ T, (DoublingMST.completeGraph n).IsSpanningTree T →
      DoublingMST.treeWeight d E ≤ DoublingMST.treeWeight d T :=
    fun T hT => hmin T (by simp [hS, hT])
  refine ⟨E, hEsp, ?_, hmin'⟩
  unfold DoublingMST.mstWeight
  symm
  apply IsLeast.csInf_eq
  refine ⟨⟨E, hEsp, rfl⟩, ?_⟩
  rintro w ⟨T, hT, rfl⟩
  exact hmin' T hT

lemma mstWeight_le (d : Fin n → Fin n → ℝ) (T : Finset (Sym2 (Fin n)))
    (hT : (DoublingMST.completeGraph n).IsSpanningTree T) :
    DoublingMST.mstWeight d ≤ DoublingMST.treeWeight d T := by
  obtain ⟨E, _, hEw, hmin⟩ := exists_mst d
  rw [← hEw]; exact hmin T hT

/-- A spanning tree crosses every proper nonempty cut. -/
lemma tree_indicator_feasible (T : Finset (Sym2 (Fin n)))
    (hT : (DoublingMST.completeGraph n).IsSpanningTree T) :
    MetricTSPSublinear.IsCutFeasible univ (fun e => if e ∈ T then (1 : ℝ) else 0) := by
  classical
  refine ⟨fun e => by dsimp only; split_ifs <;> norm_num, ?_⟩
  intro A _ hAne hAS
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hb⟩ : ∃ b, b ∉ A := by
    by_contra h
    push_neg at h
    exact hAS (Finset.eq_univ_iff_forall.mpr h)
  obtain ⟨p, hp⟩ := hT.1 a b
  obtain ⟨e, he, hcut⟩ := walk_crosses A p ha hb
  have heT := hp e he
  calc (1 : ℝ) = (if e ∈ T then (1 : ℝ) else 0) := by simp [heT]
    _ ≤ ∑ e ∈ MetricTSPSublinear.cutEdges univ A, (if e ∈ T then (1 : ℝ) else 0) :=
        Finset.single_le_sum (f := fun e => if e ∈ T then (1 : ℝ) else 0)
          (fun e _ => by split_ifs <;> norm_num) hcut

lemma tree_indicator_cost {d : Fin n → Fin n → ℝ} (T : Finset (Sym2 (Fin n)))
    (hT : (DoublingMST.completeGraph n).IsSpanningTree T) :
    ∑ e ∈ MetricTSPSublinear.pairsIn univ, DoublingMST.edgeCost d e * (if e ∈ T then (1 : ℝ) else 0)
      = DoublingMST.treeWeight d T := by
  classical
  unfold DoublingMST.treeWeight
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext e
  simp only [Finset.mem_filter, MetricTSPSublinear.pairsIn, Finset.mem_sym2_iff, Finset.mem_univ,
    implies_true, true_and]
  exact ⟨fun h => h.2, fun h => ⟨not_isDiag_of_isForest hT.2 h, h⟩⟩

lemma cutLP_obj_nonneg {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (S : Finset (Fin n))
    (x : Sym2 (Fin n) → ℝ) (hx : MetricTSPSublinear.IsCutFeasible S x) :
    0 ≤ ∑ e ∈ MetricTSPSublinear.pairsIn S, DoublingMST.edgeCost d e * x e :=
  Finset.sum_nonneg (fun e _ => mul_nonneg (edgeCost_nonneg hd e) (hx.1 e))

lemma cutLP_le {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (S : Finset (Fin n))
    (x : Sym2 (Fin n) → ℝ) (hx : MetricTSPSublinear.IsCutFeasible S x) :
    MetricTSPSublinear.cutLP d S ≤ ∑ e ∈ MetricTSPSublinear.pairsIn S, DoublingMST.edgeCost d e * x e := by
  unfold MetricTSPSublinear.cutLP
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro t ⟨y, hy, rfl⟩
    exact cutLP_obj_nonneg hd S y hy
  · exact ⟨x, hx, rfl⟩

lemma feasible_nonempty (S : Finset (Fin n)) :
    ∃ x, MetricTSPSublinear.IsCutFeasible S x := by
  classical
  refine ⟨fun _ => 1, fun _ => zero_le_one, ?_⟩
  intro A hAS hAne hAneS
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hbS, hbA⟩ : ∃ b ∈ S, b ∉ A := by
    by_contra h
    push_neg at h
    exact hAneS (Finset.Subset.antisymm hAS h)
  have hmem : s(a, b) ∈ MetricTSPSublinear.cutEdges S A :=
    Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, Finset.mem_sdiff.mpr ⟨hbS, hbA⟩⟩, rfl⟩
  calc (1 : ℝ) ≤ ∑ e ∈ MetricTSPSublinear.cutEdges S A, (fun _ => (1 : ℝ)) e :=
        Finset.single_le_sum (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) hmem

lemma le_cutLP {d : Fin n → Fin n → ℝ} (S : Finset (Fin n)) (r : ℝ)
    (h : ∀ x, MetricTSPSublinear.IsCutFeasible S x →
      r ≤ ∑ e ∈ MetricTSPSublinear.pairsIn S, DoublingMST.edgeCost d e * x e) :
    r ≤ MetricTSPSublinear.cutLP d S := by
  unfold MetricTSPSublinear.cutLP
  obtain ⟨x0, hx0⟩ := feasible_nonempty S
  refine le_csInf ⟨_, ⟨x0, hx0, rfl⟩⟩ ?_
  rintro t ⟨x, hx, rfl⟩
  exact h x hx

end MTSPBridge

end

section

/-!
Prim's total weight equals the MST weight.
-/

open scoped Classical

namespace MTSPMst
open Finset CombOpt.SpanningTree

variable {n : ℕ}

/-- Discrete layer-cake comparison: if `B ≥ 0` dominates `A` in every upper level count, then
`ΣA ≤ ΣB`. -/
lemma msum_le : ∀ (N : ℕ) (A B : Multiset ℝ), Multiset.card A = N → (∀ b ∈ B, 0 ≤ b) →
    (∀ t, 0 ≤ t → Multiset.card (A.filter (fun a => t < a)) ≤
      Multiset.card (B.filter (fun b => t < b))) →
    A.sum ≤ B.sum
  | 0, A, B, hA, hB, _ => by
    rw [Multiset.card_eq_zero.mp hA, Multiset.sum_zero]
    exact Multiset.sum_nonneg hB
  | N + 1, A, B, hA, hB, h => by
    have hA0 : A ≠ 0 := by intro h0; rw [h0] at hA; simp at hA
    obtain ⟨m, hm, hmax⟩ := Multiset.exists_max_image id hA0
    simp only [id] at hmax
    by_cases hm0 : m ≤ 0
    · have h1 : A.sum ≤ Multiset.card A • m := Multiset.sum_le_card_nsmul A m hmax
      have h2 : Multiset.card A • m ≤ 0 := by
        rw [nsmul_eq_mul]; exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hm0
      exact (h1.trans h2).trans (Multiset.sum_nonneg hB)
    push Not at hm0
    obtain ⟨A', rfl⟩ : ∃ A', A = m ::ₘ A' := ⟨_, (Multiset.cons_erase hm).symm⟩
    have hB0 : B ≠ 0 := by
      intro h0
      have := h 0 le_rfl
      rw [h0, Multiset.filter_cons_of_pos _ hm0] at this
      simp at this
    obtain ⟨m', hm', hmax'⟩ := Multiset.exists_max_image id hB0
    simp only [id] at hmax'
    have hmm' : m ≤ m' := by
      by_contra hlt
      push Not at hlt
      have := h m' (hB m' hm')
      have h1 : Multiset.filter (fun b => m' < b) B = 0 :=
        Multiset.filter_eq_nil.mpr (fun b hb => not_lt.mpr (hmax' b hb))
      rw [h1, Multiset.filter_cons_of_pos _ hlt] at this
      simp at this
    obtain ⟨B', rfl⟩ : ∃ B', B = m' ::ₘ B' := ⟨_, (Multiset.cons_erase hm').symm⟩
    rw [Multiset.sum_cons, Multiset.sum_cons]
    have ih := msum_le N A' B' (by simpa using hA)
      (fun b hb => hB b (Multiset.mem_cons_of_mem hb)) ?_
    · linarith
    intro t ht
    have ht' := h t ht
    by_cases htm : t < m
    · rw [Multiset.filter_cons_of_pos _ htm,
        Multiset.filter_cons_of_pos _ (lt_of_lt_of_le htm hmm')] at ht'
      simpa using ht'
    · have : Multiset.filter (fun a => t < a) A' = 0 :=
        Multiset.filter_eq_nil.mpr (fun a ha =>
          not_lt.mpr ((hmax a (Multiset.mem_cons_of_mem ha)).trans (not_lt.mp htm)))
      rw [this]; simp

/-- A spanning tree has at least `compCount − 1` edges longer than `t`. -/
lemma tree_count (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (T : Finset (Sym2 (Fin n))) (hT : (DoublingMST.completeGraph n).IsSpanningTree T) (t : ℝ) :
    compCount d univ t ≤ (T.filter (fun e => t < DoublingMST.edgeCost d e)).card + 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [compCount]
  set G := thrGraph d univ t with hG
  let H : SimpleGraph G.ConnectedComponent := SimpleGraph.fromRel
    (fun c1 c2 => ∃ a b, s(a, b) ∈ T ∧ G.connectedComponentMk a = c1 ∧ G.connectedComponentMk b = c2)
  have hreach : ∀ a b, H.Reachable (G.connectedComponentMk a) (G.connectedComponentMk b) := by
    intro a b
    obtain ⟨p, hp⟩ := hT.1 a b
    revert hp
    induction p with
    | nil => intro _; rfl
    | @cons x y z e he p ih =>
      intro hp
      have he' : e = s(x, y) := he
      have hyz := ih (fun e' he'' => hp e' (by simp [Graph.Walk.edges, he'']))
      by_cases hxy : G.connectedComponentMk x = G.connectedComponentMk y
      · rw [hxy]; exact hyz
      · refine SimpleGraph.Reachable.trans ?_ hyz
        apply SimpleGraph.Adj.reachable
        rw [SimpleGraph.fromRel_adj]
        refine ⟨hxy, Or.inl ⟨x, y, ?_, rfl, rfl⟩⟩
        rw [← he']; exact hp e (by simp [Graph.Walk.edges])
  have hconn : H.Connected := by
    rw [SimpleGraph.connected_iff]
    refine ⟨fun c1 c2 => ?_, ⟨G.connectedComponentMk ⟨0, hn⟩⟩⟩
    induction c1 using SimpleGraph.ConnectedComponent.ind
    induction c2 using SimpleGraph.ConnectedComponent.ind
    exact hreach _ _
  have hcardC : compCount d univ t = Nat.card G.ConnectedComponent := by
    unfold compCount
    have hrange : (↑(univ.image G.connectedComponentMk) : Set G.ConnectedComponent) = Set.univ := by
      ext c
      induction c using SimpleGraph.ConnectedComponent.ind
      simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range, Set.mem_univ, iff_true]
      exact ⟨_, rfl⟩
    rw [← hG, ← Set.ncard_coe_finset, hrange, Set.ncard_univ]
  have key : ∀ a b, s(a, b) ∈ T → G.connectedComponentMk a ≠ G.connectedComponentMk b →
      s(a, b) ∈ T.filter (fun e => t < DoublingMST.edgeCost d e) := by
    intro a b hab hne'
    rw [Finset.mem_filter]
    refine ⟨hab, ?_⟩
    rw [MTSPBridge.edgeCost_mk hd]
    by_contra hle
    push Not at hle
    apply hne'
    rw [SimpleGraph.ConnectedComponent.eq]
    apply SimpleGraph.Adj.reachable
    rw [hG, thr_adj_iff]
    refine ⟨?_, Or.inl ⟨mem_univ _, mem_univ _, hle⟩⟩
    rintro rfl; exact hne' rfl
  have hedge : H.edgeSet ⊆ ↑((T.filter (fun e => t < DoublingMST.edgeCost d e)).image
      (Sym2.map G.connectedComponentMk)) := by
    intro e he
    induction e using Sym2.ind with
    | h c1 c2 =>
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj] at he
      obtain ⟨hne, hr⟩ := he
      rw [Finset.coe_image, Set.mem_image]
      rcases hr with ⟨a, b, hab, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩
      · exact ⟨s(a, b), key a b hab hne, by simp⟩
      · exact ⟨s(a, b), key a b hab (Ne.symm hne), by simp [Sym2.eq_swap]⟩
  have h1 := hconn.card_vert_le_card_edgeSet_add_one
  have h2 : Nat.card H.edgeSet ≤ (T.filter (fun e => t < DoublingMST.edgeCost d e)).card := by
    rw [Nat.card_coe_set_eq]
    calc H.edgeSet.ncard
        ≤ (↑((T.filter (fun e => t < DoublingMST.edgeCost d e)).image
            (Sym2.map G.connectedComponentMk)) : Set _).ncard :=
          Set.ncard_le_ncard hedge (Finset.finite_toSet _)
      _ = ((T.filter (fun e => t < DoublingMST.edgeCost d e)).image
            (Sym2.map G.connectedComponentMk)).card := Set.ncard_coe_finset _
      _ ≤ _ := Finset.card_image_le
  omega

/-- Prim's edges form a forest spanning the selected set, with weight the recorded sum. -/
lemma prim_forest (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (v : Fin n) (j : ℕ) :
    ∃ F : Finset (Sym2 (Fin n)), F.card = (grun d false (fun _ => true) v j).2.length ∧
      ∑ e ∈ F, DoublingMST.edgeCost d e = ((grun d false (fun _ => true) v j).2.map Prod.snd).sum ∧
      (∀ e ∈ F, ¬ e.IsDiag ∧ ∀ x ∈ e, x ∈ (grun d false (fun _ => true) v j).1.S) ∧
      ∀ p ∈ (grun d false (fun _ => true) v j).1.S,
        (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 (Fin n)))).Reachable v p := by
  induction j with
  | zero =>
    refine ⟨∅, by simp [grun_zero], by simp [grun_zero], by simp, ?_⟩
    intro p hp
    simp only [grun_zero, ginit, Finset.mem_singleton] at hp
    rw [hp]
  | succ j ih =>
    obtain ⟨F, hFc, hFs, hFe, hFr⟩ := ih
    have I := inv_grun d false (fun _ => true) v j
    by_cases h : (cands (fun _ => true) (grun d false (fun _ => true) v j).1).Nonempty
    · rw [grun_succ_pos d false _ v j h]
      simp only
      obtain ⟨hu, -⟩ := pick_spec false (fun _ => true) h
      rw [mem_cands] at hu
      obtain ⟨p, hp, hpk⟩ := I.hex (pick false (fun _ => true) _ h)
      have hup : pick false (fun _ => true) _ h ≠ p := by rintro rfl; exact hu.2 hp
      have hnotin : s(pick false (fun _ => true) _ h, p) ∉ F := fun hm =>
        hu.2 ((hFe _ hm).2 _ (Sym2.mem_mk_left _ p))
      refine ⟨insert s(pick false (fun _ => true) _ h, p) F, ?_, ?_, ?_, ?_⟩
      · rw [card_insert_of_notMem hnotin, hFc]; simp
      · rw [sum_insert hnotin, hFs, MTSPBridge.edgeCost_mk hd, ← hpk]
        simp [add_comm]
      · intro e he
        rw [mem_insert] at he
        rcases he with rfl | he
        · refine ⟨by rw [Sym2.mk_isDiag_iff]; exact hup, ?_⟩
          intro x hx
          rw [Sym2.mem_iff] at hx
          rcases hx with rfl | rfl
          · exact mem_insert_self _ _
          · exact mem_insert_of_mem hp
        · exact ⟨(hFe e he).1, fun x hx => mem_insert_of_mem ((hFe e he).2 x hx)⟩
      · have hmono : SimpleGraph.fromEdgeSet (↑F : Set (Sym2 (Fin n))) ≤
            SimpleGraph.fromEdgeSet ↑(insert s(pick false (fun _ => true) _ h, p) F) :=
          SimpleGraph.fromEdgeSet_mono (by simp)
        intro q hq
        rw [mem_insert] at hq
        rcases hq with rfl | hq
        · have hadj : (SimpleGraph.fromEdgeSet
              ↑(insert s(pick false (fun _ => true) _ h, p) F)).Adj p (pick false (fun _ => true) _ h) := by
            rw [SimpleGraph.fromEdgeSet_adj]
            exact ⟨by simp [Sym2.eq_swap], hup.symm⟩
          exact ((hFr p hp).mono hmono).trans hadj.reachable
        · exact (hFr q hq).mono hmono
    · rw [grun_succ_neg d false _ v j h]
      exact ⟨F, hFc, hFs, hFe, hFr⟩

/-- **(c)** Prim's weight is the MST weight. -/
theorem mst_eq_prim (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (v : Fin n) :
    DoublingMST.mstWeight d = ((grun d false (fun _ => true) v (n - 1)).2.map Prod.snd).sum := by
  have hlen : (grun d false (fun _ => true) v (n - 1)).2.length = n - 1 := by
    rw [prim_length]; simp
  have hn : 0 < n := Fin.pos v
  apply le_antisymm
  · obtain ⟨F, hFc, hFs, hFe, hFr⟩ := prim_forest d hd v (n - 1)
    have I := inv_grun d false (fun _ => true) v (n - 1)
    have hc := Inv.card_S _ _ _ I
    have hSu : (grun d false (fun _ => true) v (n - 1)).1.S = univ :=
      eq_univ_of_card _ (by rw [hc, hlen, Fintype.card_fin]; omega)
    have hconn : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 (Fin n)))).Connected := by
      rw [SimpleGraph.connected_iff]
      refine ⟨fun a b => ?_, ⟨v⟩⟩
      have ha := hFr a (hSu ▸ mem_univ a)
      have hb := hFr b (hSu ▸ mem_univ b)
      exact ha.symm.trans hb
    have hEs : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 (Fin n)))).edgeSet = ↑F := by
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      ext e
      simp only [Set.mem_sdiff, mem_coe, Sym2.mem_diagSet]
      exact ⟨fun h => h.1, fun h => ⟨h, (hFe e h).1⟩⟩
    have htree : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 (Fin n)))).IsTree := by
      rw [SimpleGraph.isTree_iff_connected_and_card]
      refine ⟨hconn, ?_⟩
      rw [hEs, Nat.card_coe_set_eq, Set.ncard_coe_finset, hFc, hlen, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      omega
    have hsp := MTSPBridge.isSpanningTree_of_isTree _ htree
    replace hsp : (DoublingMST.completeGraph n).IsSpanningTree F := by
      convert hsp using 1; ext e; simp only [Set.mem_toFinset, hEs, mem_coe]
    calc DoublingMST.mstWeight d ≤ DoublingMST.treeWeight d F := MTSPBridge.mstWeight_le d F hsp
      _ = _ := hFs
  · obtain ⟨E, hE, hEw, -⟩ := MTSPBridge.exists_mst d
    rw [← hEw]
    unfold DoublingMST.treeWeight
    have hmaj := msum_le _ (↑((grun d false (fun _ => true) v (n - 1)).2.map Prod.snd))
      (E.val.map (DoublingMST.edgeCost d)) rfl ?_ ?_
    · rw [Multiset.sum_coe] at hmaj
      exact hmaj
    · intro b hb
      rw [Multiset.mem_map] at hb
      obtain ⟨e, -, rfl⟩ := hb
      exact MTSPBridge.edgeCost_nonneg hd e
    · intro t ht
      have h1 := prim_count d hd univ v (mem_univ v) t ht
      have h2 := tree_count d hd E hE t
      have hm : (fun u : Fin n => decide (u ∈ (univ : Finset (Fin n)))) = fun _ => true := by
        funext u; simp
      rw [hm, Finset.card_univ, Fintype.card_fin] at h1
      have e1 : Multiset.card (Multiset.filter (fun a => t < a)
          (↑((grun d false (fun _ => true) v (n - 1)).2.map Prod.snd) : Multiset ℝ))
          = ((grun d false (fun _ => true) v (n - 1)).2.filter (fun p => decide (t < p.2))).length := by
        rw [Multiset.filter_coe, Multiset.coe_card, List.filter_map, List.length_map]
        rfl
      have e2 : Multiset.card (Multiset.filter (fun b => t < b) (E.val.map (DoublingMST.edgeCost d)))
          = (E.filter (fun e => t < DoublingMST.edgeCost d e)).card := by
        rw [Multiset.filter_map, Multiset.card_map, Finset.card_def, Finset.filter_val]
        rfl
      rw [e1, e2]
      omega

end MTSPMst

end

section

/-!
# Prim's algorithm and farthest-first traversal (specification in `Solutions.W.MstSpec`)

* `grun_inv`   : general invariant of `grun` (any mode / mask)
* `prim_count` : (a) recorded values `> t` count threshold components (in `MstPrimA`)
* `prim_prefix`, `prim_length` : (b) prefix property (in `MstPrimA`)
* `mst_eq_prim`: (c) Prim's weight is the MST weight (in `MstPrimC`)
* `gonzalez`   : (d) farthest-first traversal
-/

open scoped Classical

namespace MTSPMst
open Finset

variable {n : ℕ}

/-- General invariant of `grun` (any mode, any mask). -/
theorem grun_inv (d : Fin n → Fin n → ℝ) (mode : Bool) (mask : Fin n → Bool) (start : Fin n)
    (j : ℕ) :
    (grun d mode mask start j).1.S
        = insert start (((grun d mode mask start j).2.map Prod.fst).toFinset) ∧
      ((grun d mode mask start j).2.map Prod.fst).Nodup ∧
      (∀ p ∈ (grun d mode mask start j).2, mask p.1 = true ∧ p.1 ≠ start) ∧
      (∀ x, (grun d mode mask start j).1.key x =
        (insert start (((grun d mode mask start j).2.map Prod.fst).toFinset)).inf'
          (Finset.insert_nonempty _ _) (fun p => d x p)) ∧
      (mask start = true → (grun d mode mask start j).2.length
        = min j ((univ.filter (fun u => mask u = true)).card - 1)) := by
  have I := inv_grun d mode mask start j
  refine ⟨I.hS, I.hnd, I.hmem, ?_, fun hs => grun_length d mode mask start hs j⟩
  intro x
  apply le_antisymm
  · apply Finset.le_inf'
    intro p hp
    rw [← I.hS] at hp
    exact I.hle x p hp
  · obtain ⟨p, hp, hpk⟩ := I.hex x
    rw [hpk]
    rw [I.hS] at hp
    exact Finset.inf'_le _ hp

/-- Farthest-first: pairwise distances of selected points dominate all current keys. -/
lemma ff_inv (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (v : Fin n) (j : ℕ) :
    ∀ a ∈ (grun d true (fun _ => true) v j).1.S, ∀ b ∈ (grun d true (fun _ => true) v j).1.S,
      a ≠ b → ∀ x, (grun d true (fun _ => true) v j).1.key x ≤ d a b := by
  induction j with
  | zero =>
    intro a ha b hb hab
    simp only [grun_zero, ginit, Finset.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | succ j ih =>
    have I := inv_grun d true (fun _ => true) v j
    by_cases h : (cands (fun _ => true) (grun d true (fun _ => true) v j).1).Nonempty
    · rw [grun_succ_pos d true _ v j h]
      simp only
      obtain ⟨hu, hbest⟩ := pick_spec true (fun _ => true) h
      rw [mem_cands] at hu
      set u := pick true (fun _ => true) (grun d true (fun _ => true) v j).1 h with hu_def
      have hku : ∀ x, (grun d true (fun _ => true) v j).1.key x ≤
          (grun d true (fun _ => true) v j).1.key u := by
        intro x
        by_cases hx : x ∈ (grun d true (fun _ => true) v j).1.S
        · have h1 := I.hle x x hx
          rw [(hd.1 x x).2 rfl] at h1
          obtain ⟨p, -, hp⟩ := I.hex u
          rw [hp]
          exact h1.trans (MTSPBridge.dist_nonneg' hd u p)
        · rw [hbest]
          exact le_bestKey_true _ h ((mem_cands _).mpr ⟨rfl, hx⟩)
      intro a ha b hb hab x
      refine (min_le_left _ _).trans ?_
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact (hku x).trans (I.hle _ b hb)
      · rw [hd.2.1]; exact (hku x).trans (I.hle _ a ha)
      · exact ih a ha b hb hab x
    · rw [grun_succ_neg d true _ v j h]
      exact ih

/-- **(d)** Farthest-first traversal with `k` points (`1 ≤ k ≤ n`). With
`P = insert v (recorded points)` and `T0 = max final key`:
`|P| = k`, `0 ≤ T0`, every point is within `T0` of `P`, `T0 = 0` if `k = n`, and if `k < n`
there are `k + 1` points with pairwise distances `≥ T0`. -/
theorem gonzalez (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (v : Fin n) (k : ℕ)
    (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (insert v (((grun d true (fun _ => true) v (k - 1)).2.map Prod.fst).toFinset)).card = k ∧
    0 ≤ (univ : Finset (Fin n)).sup' ⟨v, mem_univ v⟩ (grun d true (fun _ => true) v (k - 1)).1.key ∧
    (∀ u, ∃ p ∈ insert v (((grun d true (fun _ => true) v (k - 1)).2.map Prod.fst).toFinset),
      d u p ≤ (univ : Finset (Fin n)).sup' ⟨v, mem_univ v⟩
        (grun d true (fun _ => true) v (k - 1)).1.key) ∧
    (k = n → (univ : Finset (Fin n)).sup' ⟨v, mem_univ v⟩
        (grun d true (fun _ => true) v (k - 1)).1.key = 0) ∧
    (k < n → ∃ R : Finset (Fin n), R.card = k + 1 ∧ ∀ a ∈ R, ∀ b ∈ R, a ≠ b →
      (univ : Finset (Fin n)).sup' ⟨v, mem_univ v⟩
        (grun d true (fun _ => true) v (k - 1)).1.key ≤ d a b) := by
  have I := inv_grun d true (fun _ => true) v (k - 1)
  rw [← I.hS]
  set g := (grun d true (fun _ => true) v (k - 1)).1 with hg
  set T0 := (univ : Finset (Fin n)).sup' ⟨v, mem_univ v⟩ g.key with hT0
  have hlen := grun_length d true (fun _ => true) v rfl (k - 1)
  have hcard : g.S.card = k := by
    have hM : (univ.filter (fun u : Fin n => (fun _ => true) u = true)).card = n := by simp
    rw [Inv.card_S _ _ _ I, hlen, hM]
    omega
  have hkeyle : ∀ x, g.key x ≤ T0 := fun x => Finset.le_sup' g.key (mem_univ x)
  have hkey0 : ∀ x, 0 ≤ g.key x := by
    intro x
    obtain ⟨p, -, hp⟩ := I.hex x
    rw [hp]; exact MTSPBridge.dist_nonneg' hd x p
  have hT0nn : 0 ≤ T0 := (hkey0 v).trans (hkeyle v)
  have hkeyS : ∀ x ∈ g.S, g.key x ≤ 0 := by
    intro x hx
    have := I.hle x x hx
    rwa [(hd.1 x x).2 rfl] at this
  refine ⟨hcard, hT0nn, ?_, ?_, ?_⟩
  · intro u
    obtain ⟨p, hp, hpk⟩ := I.hex u
    exact ⟨p, hp, hpk ▸ hkeyle u⟩
  · intro hkn'
    have hSu : g.S = univ := eq_univ_of_card _ (by rw [hcard, Fintype.card_fin]; exact hkn')
    apply le_antisymm _ hT0nn
    apply Finset.sup'_le
    intro x _
    exact hkeyS x (hSu ▸ mem_univ x)
  · intro hlt
    have hpair := ff_inv d hd v (k - 1)
    rw [← hg] at hpair
    -- a point outside `g.S`, attaining `T0` if `T0 ≠ 0`
    obtain ⟨w, hwS, hw⟩ : ∃ w, w ∉ g.S ∧ T0 ≤ g.key w := by
      by_cases hz : T0 = 0
      · obtain ⟨w, hw⟩ : ∃ w, w ∉ g.S := by
          by_contra hcon
          push Not at hcon
          have : g.S = univ := eq_univ_of_forall hcon
          rw [this, Finset.card_univ, Fintype.card_fin] at hcard
          omega
        exact ⟨w, hw, hz ▸ hkey0 w⟩
      · obtain ⟨w, -, hw⟩ := Finset.exists_mem_eq_sup' (⟨v, mem_univ v⟩ : (univ : Finset (Fin n)).Nonempty) g.key
        refine ⟨w, ?_, by rw [← hT0] at hw; rw [hw]⟩
        intro hwS
        apply hz
        rw [← hT0] at hw
        exact le_antisymm (hw ▸ hkeyS w hwS) hT0nn
    refine ⟨insert w g.S, by rw [Finset.card_insert_of_notMem hwS, hcard], ?_⟩
    intro a ha b hb hab
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact hw.trans (I.hle a b hb)
    · rw [hd.2.1]; exact hw.trans (I.hle b a ha)
    · exact hw.trans (hpair a ha b hb hab w)

end MTSPMst

end

section

/-!
Tour bound: `m` points pairwise at distance `≥ τ` force `m * τ ≤ 2 * M`.
-/

open scoped Classical

namespace MTSPMst
open Finset

section path
variable {α : Type*} (d : α → α → ℝ)

/-- Cost of the path `a → l₁ → l₂ → ⋯`. -/
noncomputable def pc : α → List α → ℝ
  | _, [] => 0
  | a, b :: l => d a b + pc b l

variable {d}

lemma pc_cons_le (htri : ∀ x y z, d x z ≤ d x y + d y z) (a c : α) (X : List α) (hX : X ≠ []) :
    pc d a X ≤ d a c + pc d c X := by
  cases X with
  | nil => exact absurd rfl hX
  | cons x X' => simp only [pc]; linarith [htri a c x]

lemma pc_filter_le (htri : ∀ x y z, d x z ≤ d x y + d y z) (p : α → Bool) (b : α) :
    ∀ (l : List α) (a : α), pc d a (l.filter p ++ [b]) ≤ pc d a (l ++ [b])
  | [], _ => le_refl _
  | c :: l, a => by
    have ih := pc_filter_le htri p b l c
    by_cases hc : p c = true
    · simp only [List.filter_cons, hc, if_true, List.cons_append, pc]; linarith
    · simp only [List.filter_cons, hc, List.cons_append, pc]
      simp only [Bool.false_eq_true, if_false]
      have := pc_cons_le htri a c (l.filter p ++ [b]) (by simp)
      linarith

lemma pc_append_last (htri : ∀ x y z, d x z ≤ d x y + d y z) (a z : α) :
    ∀ (Y : List α) (x : α), pc d x (Y ++ [z]) ≤ pc d x (Y ++ [a]) + d a z
  | [], x => by simp only [List.nil_append, pc]; linarith [htri x a z]
  | y :: Y, x => by
    simp only [List.cons_append, pc]
    linarith [pc_append_last htri a z Y y]

lemma pc_closed (R : Finset α) (τ : ℝ) (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → τ ≤ d a b) (z : α)
    (hz : z ∈ R) : ∀ (Y : List α) (x : α), x ∈ R → (∀ y ∈ Y, y ∈ R) → (x :: Y).Nodup → z ∉ Y →
      (Y ≠ [] ∨ x ≠ z) → τ * (Y.length + 1) ≤ pc d x (Y ++ [z])
  | [], x, hx, _, _, _, hne => by
    simp only [List.nil_append, pc, List.length_nil]
    have : x ≠ z := by simpa using hne
    norm_num
    linarith [hR x hx z hz this]
  | y :: Y, x, hx, hY, hnd, hzY, _ => by
    simp only [List.cons_append, pc, List.length_cons]
    have hxy : x ≠ y := by
      intro h; subst h; simp at hnd
    have hyR : y ∈ R := hY y (by simp)
    have hyz : y ≠ z := by intro h; subst h; simp at hzY
    have ih := pc_closed R τ hR z hz Y y hyR (fun w hw => hY w (by simp [hw]))
      (List.nodup_cons.mp hnd).2 (by intro h; exact hzY (by simp [h])) (Or.inr hyz)
    have := hR x hx y hyR hxy
    push_cast
    linarith

lemma pc_range (g : ℕ → α) : ∀ k : ℕ,
    pc d (g 0) ((List.range k).map (fun i => g (i + 1))) =
      ∑ i ∈ Finset.range k, d (g i) (g (i + 1))
  | 0 => by simp [pc]
  | k + 1 => by
    rw [List.range_succ_eq_map, Finset.sum_range_succ']
    simp only [List.map_cons, List.map_map, pc]
    have := pc_range (fun j => g (j + 1)) k
    simp only [Function.comp_def, Nat.succ_eq_add_one, zero_add] at this ⊢
    rw [this]; ring

end path

variable {n : ℕ}

/-- Every tour through `R` (pairwise `≥ τ`, `|R| ≥ 2`) costs at least `|R| τ`. -/
lemma tourCost_ge (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (R : Finset (Fin n)) (τ : ℝ) (hτ : 0 ≤ τ) (hR2 : 2 ≤ R.card)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → τ ≤ d a b) (π : Equiv.Perm (Fin n)) :
    (R.card : ℝ) * τ ≤ MetricTSP.tourCost d π := by
  have htri : ∀ x y z, d x z ≤ d x y + d y z := hd.2.2
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; have := Finset.card_le_univ R; simp only [Fintype.card_fin] at this; omega
    · exact h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → Fin (m + 1),
      ∀ i, f i = π ⟨i % (m + 1), Nat.mod_lt _ (by omega)⟩ := ⟨_, fun _ => rfl⟩
  -- tour cost as a path
  have hcost : MetricTSP.tourCost d π = ∑ i ∈ Finset.range (m + 1), d (f i) (f (i + 1)) := by
    unfold MetricTSP.tourCost
    rw [← Fin.sum_univ_eq_sum_range (fun i => d (f i) (f (i + 1)))]
    apply Finset.sum_congr rfl
    intro i _
    rw [hf, hf]
    congr 2
    · ext; simp [Nat.mod_eq_of_lt i.isLt]
    · rw [finRotate_apply]; ext
      simp [Fin.val_add]
  set a := f 0 with ha
  set L' := (List.range m).map (fun i => f (i + 1)) with hL'
  have hpath : MetricTSP.tourCost d π = pc d a (L' ++ [a]) := by
    rw [hcost, ← pc_range (d := d) f (m + 1), List.range_succ, List.map_append]
    simp only [List.map_cons, List.map_nil]
    congr 2
    rw [ha, hf, hf]; congr 1; ext; simp
  -- nodup and membership
  have hfinj : ∀ x ∈ List.range (m + 1), ∀ y ∈ List.range (m + 1), f x = f y → x = y := by
    intro x hx y hy hxy
    simp only [List.mem_range] at hx hy
    rw [hf, hf] at hxy
    have := π.injective hxy
    simp only [Fin.mk.injEq] at this
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  have hnd : (a :: L').Nodup := by
    have := (List.nodup_range).map_on hfinj
    rw [List.range_succ_eq_map] at this
    simpa [hL', ha, List.map_map, Function.comp_def] using this
  have hmem : ∀ x, x ≠ a → x ∈ L' := by
    intro x hx
    set j := π.symm x with hj
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h0
      apply hx
      have : j = ⟨0 % (m + 1), Nat.mod_lt _ (by omega)⟩ := by ext; simp [h0]
      rw [ha, hf, ← this, hj, Equiv.apply_symm_apply]
    simp only [hL', List.mem_map, List.mem_range]
    refine ⟨(j : ℕ) - 1, by omega, ?_⟩
    rw [hf]
    have : (⟨((j : ℕ) - 1 + 1) % (m + 1), Nat.mod_lt _ (by omega)⟩ : Fin (m + 1)) = j := by
      ext; simp only; rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt j.isLt]
    rw [this, hj, Equiv.apply_symm_apply]
  set F := L'.filter (fun x => decide (x ∈ R)) with hF
  have hFnd : F.Nodup := (List.nodup_cons.mp hnd).2.filter _
  have haF : a ∉ F := fun h => (List.nodup_cons.mp hnd).1 (List.mem_of_mem_filter h)
  have hFR : ∀ y ∈ F, y ∈ R := fun y hy => by simpa using (List.mem_filter.mp hy).2
  have hFlen : (R.erase a).card ≤ F.length := by
    rw [← List.toFinset_card_of_nodup hFnd]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hxa, hxR⟩ := Finset.mem_erase.mp hx
    simp only [List.mem_toFinset, hF, List.mem_filter]
    exact ⟨hmem x hxa, by simpa using hxR⟩
  have hshort : pc d a (F ++ [a]) ≤ MetricTSP.tourCost d π := by
    rw [hpath]; exact pc_filter_le htri _ a L' a
  by_cases haR : a ∈ R
  · have hcard : (R.erase a).card + 1 = R.card := Finset.card_erase_add_one haR
    have hFne : F ≠ [] := by
      intro h; rw [h] at hFlen; simp only [List.length_nil] at hFlen; omega
    have := pc_closed R τ hR a haR F a haR hFR (List.nodup_cons.mpr ⟨haF, hFnd⟩) haF (Or.inl hFne)
    have h1 : (R.card : ℝ) ≤ F.length + 1 := by
      have : R.card ≤ F.length + 1 := by omega
      exact_mod_cast this
    nlinarith
  · have hcard : (R.erase a).card = R.card := by rw [Finset.erase_eq_of_notMem haR]
    obtain ⟨f1, F', hF1⟩ : ∃ f1 F', F = f1 :: F' := by
      cases hc : F with
      | nil => rw [hc] at hFlen; simp only [List.length_nil] at hFlen; omega
      | cons f1 F' => exact ⟨f1, F', rfl⟩
    rw [hF1] at hFlen hFnd hFR
    have hf1R : f1 ∈ R := hFR f1 (by simp)
    have hF'ne : F' ≠ [] := by
      intro h; rw [h] at hFlen; simp only [List.length_cons, List.length_nil] at hFlen; omega
    have h2 := pc_closed R τ hR f1 hf1R F' f1 hf1R (fun y hy => hFR y (by simp [hy])) hFnd
      (List.nodup_cons.mp hFnd).1 (Or.inl hF'ne)
    have h3 := pc_append_last htri a f1 F' f1
    have h4 : pc d a (F ++ [a]) = d a f1 + pc d f1 (F' ++ [a]) := by
      rw [hF1]; simp [pc]
    have h1 : (R.card : ℝ) ≤ F'.length + 1 := by
      have : R.card ≤ F'.length + 1 := by simp only [List.length_cons] at hFlen; omega
      exact_mod_cast this
    nlinarith

/-- `TSP ≤ 2 M` from Claims 3.2 and 3.3. -/
lemma tsp_le_two_mst (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) :
    MetricTSP.tspOpt d ≤ 2 * DoublingMST.mstWeight d := by
  have h2 := MetricTSPSublinear.claim_3_2 d hd
  have h3 := MetricTSPSublinear.claim_3_3 d hd
  linarith [h2.2, h3.2]

/-- **Tour bound.** `m ≥ 2` points pairwise at distance `≥ τ ≥ 0` give `m * τ ≤ 2 * M`. -/
theorem tour_bound (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (R : Finset (Fin n)) (τ : ℝ) (hτ : 0 ≤ τ) (hR2 : 2 ≤ R.card)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → τ ≤ d a b) :
    (R.card : ℝ) * τ ≤ 2 * DoublingMST.mstWeight d := by
  refine le_trans ?_ (tsp_le_two_mst d hd)
  unfold MetricTSP.tspOpt
  refine le_csInf ⟨MetricTSP.tourCost d 1, 1, rfl⟩ ?_
  rintro _ ⟨π, rfl⟩
  exact tourCost_ge d hd R τ hτ hR2 hR π

end MTSPMst

end

section

/-!
Chebyshev bound for the sample mean over uniform tuples `u : Fin r → Fin N`.
-/

open scoped Classical

namespace MTSPMst
open Finset

lemma sum_pi_prod {r N : ℕ} (h : Fin r → Fin N → ℝ) :
    ∑ u : Fin r → Fin N, ∏ k, h k (u k) = ∏ k, ∑ x, h k x := (Fintype.prod_sum h).symm

lemma cross_zero {r N : ℕ} (Y : Fin N → ℝ) (hY : ∑ x, Y x = 0) (i j : Fin r) (hij : i ≠ j) :
    ∑ u : Fin r → Fin N, Y (u i) * Y (u j) = 0 := by
  have e : ∀ u : Fin r → Fin N, Y (u i) * Y (u j) =
      ∏ k, ((if k = i then Y (u k) else 1) * (if k = j then Y (u k) else 1)) := by
    intro u
    rw [prod_mul_distrib, prod_ite_eq' univ i, prod_ite_eq' univ j]
    simp
  simp_rw [e]
  rw [sum_pi_prod (fun k x => (if k = i then Y x else 1) * (if k = j then Y x else 1))]
  apply prod_eq_zero (mem_univ i)
  simp [hij, hY]

lemma second_moment {r N : ℕ} (Y : Fin N → ℝ) (hY : ∑ x, Y x = 0) (c : ℝ)
    (hYc : ∀ x, Y x ^ 2 ≤ c ^ 2) :
    ∑ u : Fin r → Fin N, (∑ i, Y (u i)) ^ 2 ≤ r * (N ^ r * c ^ 2) := by
  have e : ∀ u : Fin r → Fin N, (∑ i, Y (u i)) ^ 2 = ∑ i, ∑ j, Y (u i) * Y (u j) := by
    intro u; rw [sq, sum_mul_sum]
  simp_rw [e]
  rw [sum_comm]
  have h2 : ∀ i : Fin r, ∑ u : Fin r → Fin N, ∑ j, Y (u i) * Y (u j) =
      ∑ u : Fin r → Fin N, Y (u i) ^ 2 := by
    intro i
    rw [sum_comm, ← add_sum_erase _ _ (mem_univ i)]
    rw [sum_eq_zero (fun j hj => cross_zero Y hY i j (ne_of_mem_erase hj).symm), add_zero]
    simp [sq]
  simp_rw [h2]
  calc ∑ i : Fin r, ∑ u : Fin r → Fin N, Y (u i) ^ 2
      ≤ ∑ _i : Fin r, ∑ _u : Fin r → Fin N, c ^ 2 :=
        sum_le_sum (fun i _ => sum_le_sum (fun u _ => hYc (u i)))
    _ = r * (N ^ r * c ^ 2) := by simp

/-- **Chebyshev over uniform tuples.** -/
theorem cheb_tuples (N r : ℕ) (hN : 1 ≤ N) (hr : 1 ≤ r) (X : Fin N → ℝ) (c a : ℝ)
    (hX0 : ∀ x, 0 ≤ X x) (hXc : ∀ x, X x ≤ c) (ha : 0 < a) :
    ((univ.filter (fun u : Fin r → Fin N =>
        a ≤ |(N / r : ℝ) * ∑ i, X (u i) - ∑ x, X x|)).card : ℝ) ≤
      N ^ r * (N ^ 2 * c ^ 2 / (r * a ^ 2)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  set μ := (∑ x, X x) / N with hμ
  set Y : Fin N → ℝ := fun x => X x - μ with hYdef
  have hμ0 : 0 ≤ μ := div_nonneg (sum_nonneg (fun x _ => hX0 x)) hN'.le
  have hμc : μ ≤ c := by
    rw [hμ, div_le_iff₀ hN']
    calc ∑ x, X x ≤ ∑ _x : Fin N, c := sum_le_sum (fun x _ => hXc x)
      _ = c * N := by simp [mul_comm]
  have hYsum : ∑ x, Y x = 0 := by
    simp only [hYdef, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hμ]
    field_simp; ring
  have hYc : ∀ x, Y x ^ 2 ≤ c ^ 2 := by
    intro x
    apply sq_le_sq'
    · simp only [hYdef]; linarith [hX0 x, hXc x]
    · simp only [hYdef]; linarith [hX0 x, hXc x]
  have hZ : ∀ u : Fin r → Fin N,
      (N / r : ℝ) * ∑ i, X (u i) - ∑ x, X x = (N / r : ℝ) * ∑ i, Y (u i) := by
    intro u
    simp only [hYdef, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hμ]
    field_simp
  have hsm := second_moment (r := r) Y hYsum c hYc
  set S := univ.filter (fun u : Fin r → Fin N => a ≤ |(N / r : ℝ) * ∑ i, X (u i) - ∑ x, X x|)
  have hmark : (S.card : ℝ) * a ^ 2 ≤ ∑ u : Fin r → Fin N, ((N / r : ℝ) * ∑ i, Y (u i)) ^ 2 := by
    calc (S.card : ℝ) * a ^ 2 = ∑ _u ∈ S, a ^ 2 := by simp
      _ ≤ ∑ u ∈ S, ((N / r : ℝ) * ∑ i, Y (u i)) ^ 2 := by
          apply sum_le_sum
          intro u hu
          have hu' := (mem_filter.mp hu).2
          rw [hZ u] at hu'
          rw [← sq_abs ((N / r : ℝ) * ∑ i, Y (u i))]
          exact pow_le_pow_left₀ ha.le hu' 2
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
  have hexp : ∑ u : Fin r → Fin N, ((N / r : ℝ) * ∑ i, Y (u i)) ^ 2 =
      (N / r : ℝ) ^ 2 * ∑ u : Fin r → Fin N, (∑ i, Y (u i)) ^ 2 := by
    rw [mul_sum]; congr 1; funext u; ring
  rw [hexp] at hmark
  have ha2 : 0 < a ^ 2 := by positivity
  have h3 : (S.card : ℝ) * a ^ 2 ≤ (N / r : ℝ) ^ 2 * (r * (N ^ r * c ^ 2)) :=
    hmark.trans (mul_le_mul_of_nonneg_left hsm (by positivity))
  rw [show (N : ℝ) ^ r * (N ^ 2 * c ^ 2 / (r * a ^ 2)) =
      ((N / r : ℝ) ^ 2 * (r * (N ^ r * c ^ 2))) / a ^ 2 by field_simp]
  rw [le_div_iff₀ ha2]; exact h3

end MTSPMst

end

section

/-!
# Analysis of the sublinear MST-weight estimator

Pure-math analysis; facts about Prim / farthest-first runs are hypotheses (abstract lists).

* `tour_bound` (MstAnaTour): `m ≥ 2` points pairwise `≥ τ ≥ 0` give `m τ ≤ 2 M`.
* `coarse_bound`: `0 ≤ A' - Σ_W (w - T1)⁺ ≤ 2 T0 (compCount d P T1 - 1)` and
  `(compCount d P T1 - 1) T1 ≤ 2 M`.
* `sum_gfull`, `hcap_bounds`, `gfull_sub_hcap_nonneg`, `sum_gfull_sub_hcap_le` (MstAnaFine).
* `cheb_tuples` (MstAnaCheb).
* `main_estimate` (θ = 5η) and `main_estimate_concrete`.
-/

open scoped Classical

namespace MTSPMst
open Finset

variable {n : ℕ}

/-- `A' = Σ_{u ∈ U} max (u - T1) 0`. -/
noncomputable def Acoarse (T1 : ℝ) (U : List ℝ) : ℝ := (U.map (fun u => max (u - T1) 0)).sum

/-- The padded per-sample value on `Fin N`: `hcap` of vertex `u` if `u < n`, else `0`. -/
noncomputable def Xpad (n N s : ℕ) (T1 : ℝ) (Lv : Fin n → List ℝ) (u : Fin N) : ℝ :=
  if h : (u : ℕ) < n then hcap n s T1 (Lv ⟨u, h⟩) else 0

lemma cnt_eq_of_count (L : List ℝ) (c : ℕ) (t : ℝ)
    (h : (L.filter (t < ·)).length + 1 = c) : cnt L t + 1 = c := by
  unfold cnt; rw [← h]; push_cast; ring

lemma dist_nonneg' (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (x y : Fin n) :
    0 ≤ d x y := by
  have h1 := hd.2.2 x y x
  have h2 := (hd.1 x x).mpr rfl
  rw [hd.2.1 y x] at h1
  linarith

lemma mst_pos (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (hn : 2 ≤ n) :
    0 < DoublingMST.mstWeight d := by
  set a : Fin n := ⟨0, by omega⟩
  set b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hpos : 0 < d a b := by
    rcases (dist_nonneg' d hd a b).lt_or_eq with h | h
    · exact h
    · exact absurd ((hd.1 a b).mp h.symm) hab
  have := tour_bound d hd {a, b} (d a b) hpos.le (by rw [card_pair hab])
    (by
      intro x hx y hy hxy
      simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact le_rfl
      · rw [hd.2.1]
      · exact absurd rfl hxy)
  rw [card_pair hab] at this
  push_cast at this
  linarith

/-- **Coarse part.** -/
theorem coarse_bound (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (W : List ℝ) (hWc : ∀ t : ℝ, 0 ≤ t → (W.filter (t < ·)).length + 1 = compCount d univ t)
    (P : Finset (Fin n)) (T0 : ℝ) (hT0 : 0 ≤ T0) (hcov : ∀ u, ∃ p ∈ P, d u p ≤ T0)
    (U : List ℝ) (hUc : ∀ t : ℝ, 0 ≤ t → (U.filter (t < ·)).length + 1 = compCount d P t)
    (T1 : ℝ) (hT01 : T0 ≤ T1) :
    (0 ≤ Acoarse T1 U - (W.map (fun w => max (w - T1) 0)).sum ∧
      Acoarse T1 U - (W.map (fun w => max (w - T1) 0)).sum ≤
        2 * T0 * ((compCount d P T1 : ℝ) - 1)) ∧
    ((compCount d P T1 : ℝ) - 1) * T1 ≤ 2 * DoublingMST.mstWeight d := by
  have hsymm := hd.2.1
  have htri := hd.2.2
  have hT1 : 0 ≤ T1 := hT0.trans hT01
  have hW' : ∀ t, 0 ≤ t → cnt W t + 1 = compCount d univ t :=
    fun t ht => cnt_eq_of_count W _ t (hWc t ht)
  have hU' : ∀ t, 0 ≤ t → cnt U t + 1 = compCount d P t :=
    fun t ht => cnt_eq_of_count U _ t (hUc t ht)
  refine ⟨?_, ?_⟩
  · have := coarse_compare W U T1 (2 * T0) hT1 (by linarith)
      (fun t ht => by
        have h1 := hW' t (hT1.trans ht)
        have h2 := hU' t (hT1.trans ht)
        have h3 : (compCount d univ t : ℝ) ≤ compCount d P t := by
          exact_mod_cast compCount_univ_le_net d hsymm P T0 t hcov (hT01.trans ht)
        linarith)
      (fun t ht => by
        have ht0 : 0 ≤ t := hT1.trans ht
        have h1 := hW' t ht0
        have h2 := hU' (t + 2 * T0) (by linarith)
        have h3 : (compCount d P (t + 2 * T0) : ℝ) ≤ compCount d univ t := by
          exact_mod_cast compCount_net_le_univ d hsymm htri P T0 t hcov hT0 ht0
        linarith)
    unfold Acoarse
    have hc := hU' T1 hT1
    refine ⟨this.1, ?_⟩
    have := this.2
    rw [← hc]; linarith
  · obtain ⟨R, -, hRc, hRsep⟩ := exists_sep_reps d hsymm P T1
    have hM0 : 0 ≤ DoublingMST.mstWeight d := by
      rcases Nat.lt_or_ge n 2 with h | h
      · -- `n ≤ 1`: no two points; the bound below only needs `M ≥ 0` when `|R| ≥ 2`
        have := MetricTSPSublinear.claim_3_2 d hd
        have h3 := MetricTSPSublinear.claim_3_3 d hd
        -- `TSP ≥ 0` is not needed: use `M/2 ≤ K ≤ M`
        linarith [this.1, this.2]
      · exact (mst_pos d hd h).le
    rcases Nat.lt_or_ge R.card 2 with h | h
    · have : (compCount d P T1 : ℝ) - 1 ≤ 0 := by
        rw [← hRc]; have : (R.card : ℝ) ≤ 1 := by exact_mod_cast (by omega : R.card ≤ 1)
        linarith
      nlinarith
    · have := tour_bound d hd R T1 hT1 h (fun a ha b hb hab => (hRsep a ha b hb hab).le)
      rw [← hRc]; nlinarith

lemma sum_min_add_max (L : List ℝ) (T : ℝ) :
    (L.map (fun w => min w T)).sum + (L.map (fun w => max (w - T) 0)).sum = L.sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    have : min x T + max (x - T) 0 = x := by
      rcases le_total x T with h | h
      · rw [min_eq_left h, max_eq_right (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left (by linarith)]; ring
    linarith

lemma sum_Xpad (N s : ℕ) (T1 : ℝ) (Lv : Fin n → List ℝ) (hN : n ≤ N) :
    ∑ x : Fin N, Xpad n N s T1 Lv x = ∑ v : Fin n, hcap n s T1 (Lv v) := by
  set G : ℕ → ℝ := fun i => if h : i < n then hcap n s T1 (Lv ⟨i, h⟩) else 0 with hG
  have e1 : ∑ x : Fin N, Xpad n N s T1 Lv x = ∑ i ∈ range N, G i := by
    rw [← Fin.sum_univ_eq_sum_range G N]; rfl
  have e2 : ∑ v : Fin n, hcap n s T1 (Lv v) = ∑ i ∈ range n, G i := by
    rw [← Fin.sum_univ_eq_sum_range G n]
    apply sum_congr rfl
    intro v _
    simp [hG, v.isLt]
  rw [e1, e2]
  symm
  apply sum_subset (range_subset_range.mpr hN)
  intro i _ hi
  simp only [mem_range, not_lt] at hi
  simp [hG, not_lt.mpr hi]

/-- **Main estimate** (θ = 5η). -/
theorem main_estimate (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (hn : 2 ≤ n)
    (W : List ℝ) (hW0 : ∀ w ∈ W, 0 ≤ w) (hWsum : DoublingMST.mstWeight d = W.sum)
    (hWc : ∀ t : ℝ, 0 ≤ t → (W.filter (t < ·)).length + 1 = compCount d univ t)
    (P : Finset (Fin n)) (T0 : ℝ) (hT0 : 0 ≤ T0) (hcov : ∀ u, ∃ p ∈ P, d u p ≤ T0)
    (U : List ℝ) (hUc : ∀ t : ℝ, 0 ≤ t → (U.filter (t < ·)).length + 1 = compCount d P t)
    (s : ℕ) (hs : 1 ≤ s) (Lv : Fin n → List ℝ)
    (hLv : ∀ v, ∀ t : ℝ, 0 ≤ t → ∀ j ≤ s, j < n →
      (j + 1 ≤ compSize d univ t v ↔ pmax (Lv v) j ≤ t))
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (r N : ℕ) (hr : 1 ≤ r) (hN : n ≤ N)
    (h_fine : n * (T0 / η) / s ≤ η * DoublingMST.mstWeight d)
    (h_var : (N : ℝ) ^ 2 * (T0 / η) ^ 2 / (r * (η * DoublingMST.mstWeight d) ^ 2) ≤ 1 / 12) :
    (11 / 12 : ℝ) * N ^ r ≤ ((univ.filter (fun u : Fin r → Fin N =>
      |Acoarse (T0 / η) U + (N / r : ℝ) * ∑ i, Xpad n N s (T0 / η) Lv (u i) - T0 / η -
        DoublingMST.mstWeight d| ≤ 5 * η * DoublingMST.mstWeight d)).card : ℝ) := by
  have hsymm := hd.2.1
  set M := DoublingMST.mstWeight d with hMdef
  set T1 := T0 / η with hT1def
  have hT1 : 0 ≤ T1 := div_nonneg hT0 hη.le
  have hT0T1 : T0 = η * T1 := by rw [hT1def]; field_simp
  have hT01 : T0 ≤ T1 := by rw [hT0T1]; nlinarith
  have hMpos : 0 < M := mst_pos d hd hn
  -- coarse
  obtain ⟨⟨hc1, hc2⟩, hc3⟩ := coarse_bound d hd W hWc P T0 hT0 hcov U hUc T1 hT01
  rw [← hMdef] at hc3
  have hcoarse : Acoarse T1 U - (W.map (fun w => max (w - T1) 0)).sum ≤ 4 * η * M := by
    calc _ ≤ 2 * T0 * ((compCount d P T1 : ℝ) - 1) := hc2
      _ = 2 * η * (((compCount d P T1 : ℝ) - 1) * T1) := by rw [hT0T1]; ring
      _ ≤ 2 * η * (2 * M) := by gcongr
      _ = 4 * η * M := by ring
  -- fine
  have hsumX : ∑ x : Fin N, Xpad n N s T1 Lv x = ∑ v : Fin n, hcap n s T1 (Lv v) :=
    sum_Xpad N s T1 Lv hN
  have hg := sum_gfull d hsymm hT1 W hW0 hWc
  have hgh := sum_gfull_sub_hcap_le d hsymm hT1 s hs Lv hLv
  have hgh0 : 0 ≤ ∑ v, (gfull d T1 v - hcap n s T1 (Lv v)) :=
    sum_nonneg (fun v _ => gfull_sub_hcap_nonneg d hsymm v hT1 s (Lv v) (hLv v))
  rw [sum_sub_distrib] at hgh hgh0
  have hMsplit := sum_min_add_max W T1
  -- Chebyshev
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcheb := cheb_tuples N r hN1 hr (Xpad n N s T1 Lv) T1 (η * M)
    (fun x => by
      unfold Xpad; split_ifs
      · exact (hcap_bounds d hsymm _ hT1 s _ (hLv _)).1
      · exact le_rfl)
    (fun x => by
      unfold Xpad; split_ifs
      · exact (hcap_bounds d hsymm _ hT1 s _ (hLv _)).2
      · exact hT1)
    (by positivity)
  set bad := univ.filter (fun u : Fin r → Fin N =>
    η * M ≤ |(N / r : ℝ) * ∑ i, Xpad n N s T1 Lv (u i) - ∑ x, Xpad n N s T1 Lv x|) with hbad
  have hbad_le : (bad.card : ℝ) ≤ N ^ r / 12 := by
    calc (bad.card : ℝ) ≤ N ^ r * (N ^ 2 * T1 ^ 2 / (r * (η * M) ^ 2)) := hcheb
      _ ≤ N ^ r * (1 / 12) := by gcongr
      _ = N ^ r / 12 := by ring
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin r → Fin N)))
    (fun u : Fin r → Fin N =>
      η * M ≤ |(N / r : ℝ) * ∑ i, Xpad n N s T1 Lv (u i) - ∑ x, Xpad n N s T1 Lv x|)
  rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hsplit
  have hsub : univ.filter (fun u : Fin r → Fin N =>
      ¬ (η * M ≤ |(N / r : ℝ) * ∑ i, Xpad n N s T1 Lv (u i) - ∑ x, Xpad n N s T1 Lv x|)) ⊆
      univ.filter (fun u : Fin r → Fin N =>
        |Acoarse T1 U + (N / r : ℝ) * ∑ i, Xpad n N s T1 Lv (u i) - T1 - M| ≤ 5 * η * M) := by
    intro u hu
    simp only [mem_filter, mem_univ, true_and, not_le] at hu ⊢
    rw [abs_lt] at hu
    rw [abs_le]
    rw [hsumX] at hu
    constructor <;> nlinarith
  have hcs := card_le_card hsub
  have hsplit' : ((univ.filter (fun u : Fin r → Fin N =>
      η * M ≤ |(N / r : ℝ) * ∑ i, Xpad n N s T1 Lv (u i) - ∑ x, Xpad n N s T1 Lv x|)).card : ℝ) +
      ((univ.filter (fun u : Fin r → Fin N =>
      ¬ (η * M ≤ |(N / r : ℝ) * ∑ i, Xpad n N s T1 Lv (u i) - ∑ x, Xpad n N s T1 Lv x|))).card : ℝ)
      = (N : ℝ) ^ r := by exact_mod_cast hsplit
  rw [← hbad] at hsplit'
  have hcs' : ((univ.filter (fun u : Fin r → Fin N =>
      ¬ (η * M ≤ |(N / r : ℝ) * ∑ i, Xpad n N s T1 Lv (u i) - ∑ x, Xpad n N s T1 Lv x|))).card : ℝ)
      ≤ ((univ.filter (fun u : Fin r → Fin N =>
        |Acoarse T1 U + (N / r : ℝ) * ∑ i, Xpad n N s T1 Lv (u i) - T1 - M| ≤ 5 * η * M)).card : ℝ) := by
    exact_mod_cast hcs
  linarith

/-- **Main estimate, concrete size conditions.** With `k = |P| ≥ q³`, `s ≥ 2q/η²`,
`r ≥ 192 q²/η⁴`, `n ≤ q⁴`, `n ≤ N ≤ 2n`, and a `(k+1)`-point `T0`-separated set (or `T0 = 0`). -/
theorem main_estimate_concrete (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (hn : 2 ≤ n)
    (W : List ℝ) (hW0 : ∀ w ∈ W, 0 ≤ w) (hWsum : DoublingMST.mstWeight d = W.sum)
    (hWc : ∀ t : ℝ, 0 ≤ t → (W.filter (t < ·)).length + 1 = compCount d univ t)
    (P : Finset (Fin n)) (T0 : ℝ) (hT0 : 0 ≤ T0) (hcov : ∀ u, ∃ p ∈ P, d u p ≤ T0)
    (hsep : T0 = 0 ∨ ∃ R : Finset (Fin n), R.card = P.card + 1 ∧
      ∀ a ∈ R, ∀ b ∈ R, a ≠ b → T0 ≤ d a b)
    (U : List ℝ) (hUc : ∀ t : ℝ, 0 ≤ t → (U.filter (t < ·)).length + 1 = compCount d P t)
    (s : ℕ) (Lv : Fin n → List ℝ)
    (hLv : ∀ v, ∀ t : ℝ, 0 ≤ t → ∀ j ≤ s, j < n →
      (j + 1 ≤ compSize d univ t v ↔ pmax (Lv v) j ≤ t))
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (r N : ℕ) (hN : n ≤ N)
    (q : ℝ) (hq : 0 < q) (hkq : q ^ 3 ≤ P.card) (hsq : 2 * q / η ^ 2 ≤ s)
    (hrq : 192 * q ^ 2 / η ^ 4 ≤ r) (hnq : (n : ℝ) ≤ q ^ 4) (hNn : N ≤ 2 * n) :
    (11 / 12 : ℝ) * N ^ r ≤ ((univ.filter (fun u : Fin r → Fin N =>
      |Acoarse (T0 / η) U + (N / r : ℝ) * ∑ i, Xpad n N s (T0 / η) Lv (u i) - T0 / η -
        DoublingMST.mstWeight d| ≤ 5 * η * DoublingMST.mstWeight d)).card : ℝ) := by
  set M := DoublingMST.mstWeight d with hMdef
  set T1 := T0 / η with hT1def
  have hMpos : 0 < M := mst_pos d hd hn
  have hT1 : 0 ≤ T1 := div_nonneg hT0 hη.le
  have hT0T1 : T0 = η * T1 := by rw [hT1def]; field_simp
  have hη2 : 0 < η ^ 2 := by positivity
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le (by positivity) hsq
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le (by positivity) hrq
  have hs : 1 ≤ s := by
    have : 0 < s := by exact_mod_cast hspos
    omega
  have hr : 1 ≤ r := by
    have : 0 < r := by exact_mod_cast hrpos
    omega
  -- `k T0 ≤ 2 M`
  have hkT0 : (P.card : ℝ) * T0 ≤ 2 * M := by
    rcases hsep with h0 | ⟨R, hRc, hR⟩
    · rw [h0]; simp; linarith
    · have hk1 : 1 ≤ P.card := by
        have : (0 : ℝ) < P.card := lt_of_lt_of_le (by positivity) hkq
        exact_mod_cast this
      have := tour_bound d hd R T0 hT0 (by omega) hR
      rw [hRc] at this; push_cast at this
      nlinarith
  have hq3 : q ^ 3 * T1 * η ≤ 2 * M := by
    have : q ^ 3 * T0 ≤ P.card * T0 := mul_le_mul_of_nonneg_right hkq hT0
    rw [hT0T1] at this hkT0; nlinarith
  have hnT : (n : ℝ) * T1 * η ≤ 2 * q * M := by
    have h1 : (n : ℝ) * (T1 * η) ≤ q ^ 4 * (T1 * η) :=
      mul_le_mul_of_nonneg_right hnq (by positivity)
    have h2 : q ^ 4 * (T1 * η) = q * (q ^ 3 * T1 * η) := by ring
    nlinarith
  apply main_estimate d hd hn W hW0 hWsum hWc P T0 hT0 hcov U hUc s hs Lv hLv η hη hη1 r N hr hN
  · -- `n T1 / s ≤ η M`
    rw [div_le_iff₀ hspos]
    have hs2 : 2 * q ≤ s * η ^ 2 := by rwa [div_le_iff₀ hη2] at hsq
    have b1 : 2 * q * M ≤ s * η ^ 2 * M := mul_le_mul_of_nonneg_right hs2 hMpos.le
    have b2 : ((n : ℝ) * T1) * η ≤ (η * M * s) * η := by
      calc ((n : ℝ) * T1) * η ≤ 2 * q * M := hnT
        _ ≤ s * η ^ 2 * M := b1
        _ = (η * M * s) * η := by ring
    exact le_of_mul_le_mul_right b2 hη
  · -- variance condition
    have hr4 : 192 * q ^ 2 ≤ r * η ^ 4 := by rwa [div_le_iff₀ (by positivity)] at hrq
    have hN2 : (N : ℝ) ≤ 2 * q ^ 4 := by
      have : (N : ℝ) ≤ 2 * n := by exact_mod_cast hNn
      linarith
    have hNT : (N : ℝ) * T1 * η ≤ 4 * q * M := by
      have h1 : (N : ℝ) * (T1 * η) ≤ 2 * q ^ 4 * (T1 * η) :=
        mul_le_mul_of_nonneg_right hN2 (by positivity)
      have h2 : 2 * q ^ 4 * (T1 * η) = 2 * q * (q ^ 3 * T1 * η) := by ring
      nlinarith
    have hNT0 : 0 ≤ (N : ℝ) * T1 * η := by positivity
    have hsq' : ((N : ℝ) * T1 * η) ^ 2 ≤ (4 * q * M) ^ 2 := pow_le_pow_left₀ hNT0 hNT 2
    rw [div_le_iff₀ (by positivity)]
    have a1 : 12 * ((N : ℝ) * T1 * η) ^ 2 ≤ 12 * (4 * q * M) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq' (by norm_num)
    have a2 : 192 * q ^ 2 * M ^ 2 ≤ r * η ^ 4 * M ^ 2 := mul_le_mul_of_nonneg_right hr4 (sq_nonneg M)
    have a3 : (12 * (N : ℝ) ^ 2 * T1 ^ 2) * η ^ 2 ≤ (r * η ^ 2 * M ^ 2) * η ^ 2 := by
      calc (12 * (N : ℝ) ^ 2 * T1 ^ 2) * η ^ 2 = 12 * ((N : ℝ) * T1 * η) ^ 2 := by ring
        _ ≤ 12 * (4 * q * M) ^ 2 := a1
        _ = 192 * q ^ 2 * M ^ 2 := by ring
        _ ≤ r * η ^ 4 * M ^ 2 := a2
        _ = (r * η ^ 2 * M ^ 2) * η ^ 2 := by ring
    have a4 := le_of_mul_le_mul_right a3 hη2
    have e : (r : ℝ) * (η * M) ^ 2 = r * η ^ 2 * M ^ 2 := by ring
    rw [e]; linarith

end MTSPMst

end

section

open scoped Classical

namespace MTSPGlue
open MTSPMst MTSPEst Finset

variable {n : ℕ}

lemma metric_nonneg {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (x y : Fin n) : 0 ≤ d x y := by
  have h := hd.2.2 x y x
  rw [hd.2.1 y x, (hd.1 x x).mpr rfl] at h
  linarith

lemma key_nonneg {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (mode : Bool) (mask : Fin n → Bool)
    (start : Fin n) (j : ℕ) (x : Fin n) : 0 ≤ (grun d mode mask start j).1.key x := by
  rw [(grun_inv d mode mask start j).2.2.2.1 x]
  apply Finset.le_inf'
  intro p _; exact metric_nonneg hd x p

lemma vals_nonneg {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (mode : Bool) (mask : Fin n → Bool)
    (start : Fin n) : ∀ j, ∀ p ∈ (grun d mode mask start j).2, 0 ≤ p.2 := by
  intro j
  induction j with
  | zero => simp [grun]
  | succ j ih =>
    by_cases h : (cands mask (grun d mode mask start j).1).Nonempty
    · rw [grun_succ_pos d mode mask start j h]
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact ih p hp
      · rw [List.mem_singleton] at hp; subst hp; exact key_nonneg hd _ _ _ _ _
    · rw [grun_succ_neg d mode mask start j h]; exact ih

lemma filter_map_snd (L : List (Fin n × ℝ)) (t : ℝ) :
    ((L.map Prod.snd).filter (t < ·)).length = (L.filter (fun p => decide (t < p.2))).length := by
  rw [List.filter_map, List.length_map]; rfl

lemma sum_range_getD (L : List ℝ) (f : ℝ → ℝ) :
    ∑ j ∈ range L.length, f (L.getD j 0) = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]; ring

lemma foldl_max_le (l : List ℕ) (g : ℕ → ℝ) (a c : ℝ) (ha : a ≤ c) (hg : ∀ x ∈ l, g x ≤ c) :
    l.foldl (fun b u => max b (g u)) a ≤ c := by
  induction l generalizing a with
  | nil => simpa
  | cons x l ih =>
    simp only [List.foldl_cons]
    exact ih _ (max_le ha (hg x (by simp))) (fun y hy => hg y (by simp [hy]))

lemma le_foldl_max (l : List ℕ) (g : ℕ → ℝ) (a : ℝ) : a ≤ l.foldl (fun b u => max b (g u)) a ∧
    ∀ x ∈ l, g x ≤ l.foldl (fun b u => max b (g u)) a := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (max a (g x))
    refine ⟨(le_max_left _ _).trans h1, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact (le_max_right _ _).trans h1
    · exact h2 y hy

/-- `T0` of the code equals the max final key of the farthest-first run. -/
lemma T0_eq (K1 : ℕ) {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (h : 0 < n) :
    T0 K1 d h = (univ : Finset (Fin n)).sup' ⟨⟨0, h⟩, mem_univ _⟩
      (grun d true (fun _ => true) ⟨0, h⟩ (kOf K1 n - 1)).1.key := by
  apply le_antisymm
  · apply foldl_max_le
    · obtain ⟨u⟩ : Nonempty (Fin n) := ⟨⟨0, h⟩⟩
      exact (key_nonneg hd _ _ _ _ ⟨0, h⟩).trans (Finset.le_sup' _ (mem_univ _))
    · intro x hx
      have hxn : x < n := List.mem_range.mp hx
      simp only [keyN, run1, allOnes, dif_pos hxn]
      exact Finset.le_sup' (fun u => (grun d true (fun _ => true) ⟨0, h⟩ (kOf K1 n - 1)).1.key u)
        (mem_univ (⟨x, hxn⟩ : Fin n))
  · apply Finset.sup'_le
    intro u _
    have := (le_foldl_max (List.range n) (keyN (run1 K1 d h).1) 0).2 u (List.mem_range.mpr u.isLt)
    have hk : keyN (run1 K1 d h).1 (u : ℕ) = (grun d true (fun _ => true) ⟨0, h⟩ (kOf K1 n - 1)).1.key u := by
      simp [keyN, run1, u.isLt]; rfl
    rw [hk] at this
    exact this

/-- The net of the code as a finset. -/
lemma netP_finset (K1 : ℕ) (d : Fin n → Fin n → ℝ) (h : 0 < n) :
    univ.filter (fun u => netP K1 d h u = true) =
      insert ⟨0, h⟩ ((((grun d true (fun _ => true) ⟨0, h⟩ (kOf K1 n - 1)).2.map Prod.fst).toFinset)) := by
  ext u
  simp only [mem_filter, mem_univ, true_and, mem_insert, List.mem_toFinset, Fin.ext_iff]
  unfold netP run1 allOnes
  simp only [decide_eq_true_eq]

theorem est_good (S1 R1 : ℕ) (η : ℚ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hS1 : (2 : ℝ) / (η : ℝ) ^ 2 ≤ S1) (hR1 : (192 : ℝ) / (η : ℝ) ^ 4 ≤ R1) (hS1' : 1 ≤ S1) (hR1' : 1 ≤ R1)
    (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (hn : 2 ≤ n) :
    (11 / 12 : ℝ) * ((2 ^ mOf n : ℕ) : ℝ) ^ (rOf R1 n) ≤
      ((univ.filter (fun u : Fin (rOf R1 n) → Fin (2 ^ mOf n) =>
        |A' 1 (1 / η) d (by omega) + ((2 ^ mOf n : ℕ) / (rOf R1 n) : ℝ) *
            ∑ i, X 1 S1 (1 / η) d (by omega) (u i) - T1 1 (1 / η) d (by omega) -
          DoublingMST.mstWeight d| ≤ 5 * (η : ℝ) * DoublingMST.mstWeight d)).card : ℝ) := by
  have h0 : 0 < n := by omega
  have hηr : (0 : ℝ) < η := by exact_mod_cast hη
  have hηr1 : (η : ℝ) ≤ 1 := by exact_mod_cast hη1
  set v0 : Fin n := ⟨0, h0⟩ with hv0
  -- full Prim
  set W := ((grun d false (fun _ => true) v0 (n - 1)).2.map Prod.snd) with hWdef
  have hW0 : ∀ w ∈ W, 0 ≤ w := by
    intro w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    exact vals_nonneg hd _ _ _ _ p hp
  have hWsum : DoublingMST.mstWeight d = W.sum := mst_eq_prim d hd v0
  have hWc : ∀ t : ℝ, 0 ≤ t → (W.filter (t < ·)).length + 1 = compCount d univ t := by
    intro t ht
    have := prim_count d hd univ v0 (mem_univ _) t ht
    simp only [card_univ, Fintype.card_fin, mem_univ, decide_true] at this
    rw [hWdef, filter_map_snd]; exact this
  -- the net
  set k := kOf 1 n with hk
  have hk1 : 1 ≤ k := by
    simp only [hk, kOf, one_mul]
    exact le_min (by omega) (Nat.one_le_pow _ _ (qOf_pos n))
  have hkn : k ≤ n := min_le_left _ _
  obtain ⟨hPc, hT0nn, hcov, hkeq, hklt⟩ := gonzalez d hd v0 k hk1 hkn
  set P := univ.filter (fun u => netP 1 d h0 u = true) with hPdef
  have hPeq := netP_finset 1 d h0
  rw [← hPdef] at hPeq
  have hT0 := T0_eq 1 hd h0
  set T0v := T0 1 d h0 with hT0v
  rw [← hPeq] at hPc hcov
  rw [← hT0] at hT0nn hcov hkeq hklt
  have hmaskP : netP 1 d h0 = (fun u => decide (u ∈ P)) := by
    funext u; simp [hPdef]
  have hv0P : v0 ∈ P := by rw [hPeq]; exact mem_insert_self _ _
  set Ul := U 1 d h0 with hUl
  have hUc : ∀ t : ℝ, 0 ≤ t → (Ul.filter (t < ·)).length + 1 = compCount d P t := by
    intro t ht
    have := prim_count d hd P v0 hv0P t ht
    rw [hPc] at this
    rw [hUl, U, run2, hmaskP, filter_map_snd]; exact this
  set Lv : Fin n → List ℝ := fun v => (run3 S1 d v).2.map Prod.snd with hLvdef
  have hLv : ∀ v, ∀ t : ℝ, 0 ≤ t → ∀ j ≤ sOf S1 n, j < n →
      (j + 1 ≤ compSize d univ t v ↔ pmax (Lv v) j ≤ t) :=
    fun v t ht j hj hjn => prim_prefix d hd v (sOf S1 n) t ht j hj hjn
  -- identify the code quantities
  have hT1 : T1 1 (1 / η) d h0 = T0v / η := by
    simp only [T1, hT0v]; push_cast; ring
  have hA : A' 1 (1 / η) d h0 = Acoarse (T0v / η) Ul := by
    rw [A', hT1, Acoarse, sum_range_getD Ul (fun u => max (u - T0v / η) 0)]
  have hX : ∀ u : Fin (2 ^ mOf n), X 1 S1 (1 / η) d h0 u = Xpad n (2 ^ mOf n) (sOf S1 n) (T0v / η) Lv u := by
    intro u
    simp only [X, Xpad, MTSPEst.hcap, hT1, hLvdef]
  have hN : n ≤ 2 ^ mOf n := mOf_spec n
  have hNn : 2 ^ mOf n ≤ 2 * n := by
    have hm : 1 ≤ mOf n := by
      by_contra hc
      have : mOf n = 0 := by omega
      have := mOf_spec n; rw [‹mOf n = 0›] at this; simp at this; omega
    have := mOf_min n (mOf n - 1) (by omega)
    have h2 : 2 ^ mOf n = 2 * 2 ^ (mOf n - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have hs1 : 1 ≤ sOf S1 n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by have := qOf_pos n; omega))
  have hr1 : 1 ≤ rOf R1 n := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by have := qOf_pos n; omega)))
  have hrw : ∀ u : Fin (rOf R1 n) → Fin (2 ^ mOf n),
      (|A' 1 (1 / η) d h0 + ((2 ^ mOf n : ℕ) / (rOf R1 n) : ℝ) * ∑ i, X 1 S1 (1 / η) d h0 (u i) -
          T1 1 (1 / η) d h0 - DoublingMST.mstWeight d| ≤ 5 * (η : ℝ) * DoublingMST.mstWeight d) ↔
      (|Acoarse (T0v / η) Ul + ((2 ^ mOf n : ℕ) / (rOf R1 n) : ℝ) *
          ∑ i, Xpad n (2 ^ mOf n) (sOf S1 n) (T0v / η) Lv (u i) - T0v / η -
          DoublingMST.mstWeight d| ≤ 5 * (η : ℝ) * DoublingMST.mstWeight d) := by
    intro u
    rw [hA, hT1]
    simp only [hX]
  simp only [hrw]
  have hM0 : 0 ≤ DoublingMST.mstWeight d := by
    rw [hWsum]; exact List.sum_nonneg hW0
  by_cases hq : qOf n ^ 3 ≤ n
  · have hkq : k = qOf n ^ 3 := by simp [hk, kOf, min_eq_right hq]
    have hsep : T0v = 0 ∨ ∃ R : Finset (Fin n), R.card = P.card + 1 ∧
        ∀ a ∈ R, ∀ b ∈ R, a ≠ b → T0v ≤ d a b := by
      rcases lt_or_eq_of_le hkn with hlt | heq
      · right; rw [hPc]; exact hklt hlt
      · left; exact hkeq heq
    have hq0 : (0 : ℝ) < qOf n := by exact_mod_cast qOf_pos n
    have := main_estimate_concrete d hd hn W hW0 hWsum hWc P T0v hT0nn hcov hsep Ul hUc (sOf S1 n) Lv hLv
      (η : ℝ) hηr hηr1 (rOf R1 n) (2 ^ mOf n) hN (qOf n : ℝ) hq0
      (by rw [hPc, hkq]; push_cast; rfl)
      (by
        simp only [sOf]; push_cast
        have h2 : 2 ≤ (S1 : ℝ) * (η : ℝ) ^ 2 := by
          rw [div_le_iff₀ (by positivity)] at hS1; linarith
        rw [div_le_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_left h2 hq0.le
        nlinarith [this])
      (by
        simp only [rOf]; push_cast
        have h2 : 192 ≤ (R1 : ℝ) * (η : ℝ) ^ 4 := by
          rw [div_le_iff₀ (by positivity)] at hR1; linarith
        rw [div_le_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_left h2 (sq_nonneg (qOf n : ℝ))
        nlinarith [this])
      (by exact_mod_cast qOf_spec n) hNn
    simpa using this
  · have hkn' : k = n := by simp only [hk, kOf, one_mul]; exact min_eq_left (by omega)
    have hT0z : T0v = 0 := hkeq hkn'
    have := main_estimate d hd hn W hW0 hWsum hWc P T0v hT0nn hcov Ul hUc (sOf S1 n) hs1 Lv hLv
      (η : ℝ) hηr hηr1 (rOf R1 n) (2 ^ mOf n) hr1 hN
      (by rw [hT0z]; simp; positivity)
      (by rw [hT0z]; simp)
    simpa using this

end MTSPGlue

end

section

/-!
Composition of `SublinearSteiner` programs.

A program is *relocated* into slot `s ∈ {1,2}` and memory parity `b ∈ {0,1}`:
register / pointer `i` becomes `3*i + s`, memory cells (real and integer) `x` become `2*x + b`,
program positions are shifted to `base + posOf`, and `halt src` becomes
"`r[OUT] := r[src']`, jump to `cont`". Slot `0` indices (`3*k`) are global:
register `ZR = 0` is never written (stays `0`), register `OUT = 3` receives outputs,
pointer `S0 = 0` is the address scratch pointer.
-/

namespace MTSPComp
open SublinearSteiner SmaleNinth

/-- Renaming of register / pointer indices for slot `s`. -/
def rr (s i : ℕ) : ℕ := 3 * i + s

/-- Global zero register (never written). -/
def ZR : ℕ := 0
/-- Global output register of relocated halts. -/
def OUT : ℕ := 3
/-- Global scratch pointer for address computation. -/
def S0 : ℕ := 0

/-- `p[S0] := 2 * p[q] + b`. -/
def addrCode (b q : ℕ) : List Instr :=
  .pointerAdd S0 q q :: (if b = 1 then [.core (.pinc S0)] else [])

/-- Length of the block of an instruction (independent of the jump map). -/
def blen (b : ℕ) : Instr → ℕ
  | .core (.load _ _) => (addrCode b 0).length + 1
  | .core (.store _ _) => (addrCode b 0).length + 1
  | .integerLoad _ _ => (addrCode b 0).length + 1
  | .integerStore _ _ => (addrCode b 0).length + 1
  | .halt _ => 2
  | _ => 1

/-- Position of original instruction `k` of `P` in the relocated code. -/
def posOf (b : ℕ) (P : Program) (base k : ℕ) : ℕ :=
  base + ((P.take k).map (blen b)).sum

/-- Total length of the relocated code. -/
def rlen (b : ℕ) (P : Program) : ℕ := (P.map (blen b)).sum

/-- The block replacing one instruction. `pos` maps original jump targets, `cont` is the
continuation of halts. -/
def block (s b : ℕ) (pos : ℕ → ℕ) (cont : ℕ) : Instr → List Instr
  | .core (.const d c) => [.core (.const (rr s d) c)]
  | .core (.add d i j) => [.core (.add (rr s d) (rr s i) (rr s j))]
  | .core (.sub d i j) => [.core (.sub (rr s d) (rr s i) (rr s j))]
  | .core (.mul d i j) => [.core (.mul (rr s d) (rr s i) (rr s j))]
  | .core (.div d i j) => [.core (.div (rr s d) (rr s i) (rr s j))]
  | .core (.load d q) => addrCode b (rr s q) ++ [.core (.load (rr s d) S0)]
  | .core (.store q i) => addrCode b (rr s q) ++ [.core (.store S0 (rr s i))]
  | .core (.pset q c) => [.core (.pset (rr s q) c)]
  | .core (.pcopy q q') => [.core (.pcopy (rr s q) (rr s q'))]
  | .core (.pinc q) => [.core (.pinc (rr s q))]
  | .core (.pdec q) => [.core (.pdec (rr s q))]
  | .core (.jle i t) => [.core (.jle (rr s i) (pos t))]
  | .core (.pjle q q' t) => [.core (.pjle (rr s q) (rr s q') (pos t))]
  | .core .accept => [.core .accept]
  | .core .reject => [.core .reject]
  | .pointerAdd d a c => [.pointerAdd (rr s d) (rr s a) (rr s c)]
  | .pointerSub d a c => [.pointerSub (rr s d) (rr s a) (rr s c)]
  | .integerLoad d a => addrCode b (rr s a) ++ [.integerLoad (rr s d) S0]
  | .integerStore a c => addrCode b (rr s a) ++ [.integerStore S0 (rr s c)]
  | .pointerReal d a => [.pointerReal (rr s d) (rr s a)]
  | .coin d => [.coin (rr s d)]
  | .query d a c => [.query (rr s d) (rr s a) (rr s c)]
  | .halt src => [.core (.add OUT (rr s src) ZR), .core (.pjle S0 S0 cont)]

/-- The relocated program (to be placed at position `base`). -/
def reloc (s b : ℕ) (P : Program) (base cont : ℕ) : Program :=
  (P.map (block s b (posOf b P base) cont)).flatten

/-- Copy loop: for `x = n, n-1, …, 0`: `I[2x] := I[x]`, `I[2x+1] := I[x]`. Uses pointers 3,6,9,12,15.
Positions `0 … 11`; exits to position `12`. -/
def copyCode : Program :=
  [ .core (.pset 6 0),            -- 0: p6 := 0
    .integerLoad 3 6,             -- 1: p3 := I[0] = n
    .core (.pset 9 0),            -- 2: p9 := 0
    .core (.pjle 9 3 5),          -- 3: if 0 ≤ x goto 5
    .core (.pjle 9 9 12),         -- 4: goto 12
    .integerLoad 12 3,            -- 5: p12 := I[x]
    .pointerAdd 15 3 3,           -- 6: p15 := 2x
    .integerStore 15 12,          -- 7: I[2x] := p12
    .core (.pinc 15),             -- 8: p15 := 2x+1
    .integerStore 15 12,          -- 9: I[2x+1] := p12
    .core (.pdec 3),              -- 10: x := x - 1
    .core (.pjle 9 9 3) ]         -- 11: goto 3

/-- Middle code: `M[0] := r[OUT]`, `r[6] := r[OUT]`. -/
def midCode : Program :=
  [ .core (.pset 3 0), .core (.store 3 OUT), .core (.add 6 OUT ZR) ]

/-- Tail: with `M̂ = r[6]`, `L = r[OUT]`, halt with `2 M̂` if `(1+e)/2 · M̂ ≤ L`, else `(2-e) M̂`.
Positions relative to the start `t0` of the tail. -/
def tailCode (e : ℚ) (t0 : ℕ) : Program :=
  [ .core (.const 9 (((1 + e) / 2 : ℚ) : ℝ)),   -- t0
    .core (.mul 12 9 6),                          -- t0+1
    .core (.sub 12 12 OUT),                       -- t0+2
    .core (.jle 12 (t0 + 7)),                     -- t0+3
    .core (.const 15 (((2 - e) : ℚ) : ℝ)),       -- t0+4
    .core (.mul 18 15 6),                         -- t0+5
    .halt 18,                                     -- t0+6
    .core (.const 15 ((2 : ℚ) : ℝ)),             -- t0+7
    .core (.mul 18 15 6),                         -- t0+8
    .halt 18 ]                                    -- t0+9

/-- Position of the middle code. -/
def midPos (P1 : Program) : ℕ := copyCode.length + rlen 1 P1
/-- Start of the second relocated program. -/
def base2 (P1 : Program) : ℕ := midPos P1 + midCode.length
/-- Start of the tail. -/
def tailPos (P1 P2 : Program) : ℕ := base2 P1 + rlen 0 P2

/-- The composite program: copy loop, `P1` (slot 1, odd cells), middle, `P2` (slot 2, even
cells), decision tail. -/
def composite (e : ℚ) (P1 P2 : Program) : Program :=
  copyCode ++ reloc 1 1 P1 copyCode.length (midPos P1) ++ midCode ++
    reloc 2 0 P2 (base2 P1) (tailPos P1 P2) ++ tailCode e (tailPos P1 P2)

end MTSPComp

end

section

namespace MTSPComp
open SublinearSteiner SmaleNinth

section general
variable (P : Program) {n : ℕ} (w : Fin n → Fin n → ℝ) (f : ℕ → Bool)

lemma step_halted (σ : State) (z : ℝ) (h : σ.output = some z) : step P w f σ = σ := by
  simp [step, h]

lemma iterate_halted (σ : State) (z : ℝ) (h : σ.output = some z) (t : ℕ) :
    (step P w f)^[t] σ = σ :=
  Function.iterate_fixed (step_halted P w f σ z h) t

lemma output_stable (σ : State) (z : ℝ) (t t' : ℕ)
    (h : ((step P w f)^[t] σ).output = some z) (htt : t ≤ t') :
    ((step P w f)^[t'] σ).output = some z := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htt
  rw [add_comm, Function.iterate_add_apply, iterate_halted P w f _ z h, h]

lemma step_coins_le (σ : State) : (step P w f σ).coins ≤ σ.coins + 1 := by
  unfold step
  split
  · simp
  · split <;> simp [State.next]

lemma step_coins_mono (σ : State) : σ.coins ≤ (step P w f σ).coins := by
  unfold step
  split
  · simp
  · split <;> simp [State.next]

lemma step_queries_le (σ : State) : (step P w f σ).queries ≤ σ.queries + 1 := by
  unfold step
  split
  · simp
  · split <;> simp [State.next]

lemma coins_le (σ : State) (t : ℕ) : ((step P w f)^[t] σ).coins ≤ σ.coins + t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have := step_coins_le P w f ((step P w f)^[t] σ)
    omega

lemma coins_mono (σ : State) (t t' : ℕ) (htt : t ≤ t') :
    ((step P w f)^[t] σ).coins ≤ ((step P w f)^[t'] σ).coins := by
  induction t' with
  | zero => rw [Nat.le_zero.1 htt]
  | succ t' ih =>
    rcases Nat.of_le_succ htt with h | h
    · rw [Function.iterate_succ_apply']
      exact (ih h).trans (step_coins_mono P w f _)
    · rw [h]

lemma queries_le (σ : State) (t : ℕ) : ((step P w f)^[t] σ).queries ≤ σ.queries + t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have := step_queries_le P w f ((step P w f)^[t] σ)
    omega

lemma step_congr_tape (f' : ℕ → Bool) (σ : State)
    (h : ∀ j < (step P w f σ).coins, f j = f' j) : step P w f σ = step P w f' σ := by
  unfold step at h ⊢
  rcases ho : σ.output with _ | _ <;> simp only [ho] at h ⊢
  · rcases hP : P[σ.cfg.pc]? with _ | ins <;> simp only [hP] at h ⊢
    cases ins <;> simp only at h ⊢
    rw [h σ.coins (by simp)]

lemma iterate_congr_tape (f' : ℕ → Bool) (σ : State) (t : ℕ)
    (h : ∀ j < ((step P w f)^[t] σ).coins, f j = f' j) :
    (step P w f)^[t] σ = (step P w f')^[t] σ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply'] at h ⊢
    rw [Function.iterate_succ_apply']
    have hm := step_coins_mono P w f ((step P w f)^[t] σ)
    rw [← ih (fun j hj => h j (lt_of_lt_of_le hj hm))]
    exact step_congr_tape P w f f' _ h

end general

section layout

lemma addrCode_length (b q : ℕ) : (addrCode b q).length = (addrCode b 0).length := by
  unfold addrCode; split <;> simp

lemma block_length (s b : ℕ) (pos : ℕ → ℕ) (cont : ℕ) (i : Instr) :
    (block s b pos cont i).length = blen b i := by
  rcases i with i | _ | _ | _ | _ | _ | _ | _ | _
  · cases i <;> simp [block, blen, addrCode_length]
  all_goals simp [block, blen, addrCode_length]

lemma reloc_length_glue (s b : ℕ) (P : Program) (base cont : ℕ) :
    (reloc s b P base cont).length = rlen b P := by
  simp [reloc, rlen, List.length_flatten, Function.comp_def, block_length]

lemma copyCode_length : copyCode.length = 12 := rfl
lemma midCode_length : midCode.length = 3 := rfl
lemma tailCode_length (e : ℚ) (t0 : ℕ) : (tailCode e t0).length = 10 := rfl

variable (e : ℚ) (P1 P2 : Program)

lemma composite_eq : composite e P1 P2 = copyCode ++ (reloc 1 1 P1 copyCode.length (midPos P1) ++
    (midCode ++ (reloc 2 0 P2 (base2 P1) (tailPos P1 P2) ++ tailCode e (tailPos P1 P2)))) := by
  simp [composite]

lemma composite_copy : ∀ k < 12, (composite e P1 P2)[k]? = copyCode[k]? := by
  intro k hk
  rw [composite_eq, List.getElem?_append_left (by rw [copyCode_length]; exact hk)]

lemma composite_r1 : ∀ k < rlen 1 P1, (composite e P1 P2)[copyCode.length + k]? =
    (reloc 1 1 P1 copyCode.length (midPos P1))[k]? := by
  intro k hk
  rw [composite_eq, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left (by rw [reloc_length_glue]; exact hk)]

lemma composite_mid : ∀ k < 3, (composite e P1 P2)[midPos P1 + k]? = midCode[k]? := by
  intro k hk
  rw [composite_eq, List.getElem?_append_right (by unfold midPos; omega),
    List.getElem?_append_right (by rw [reloc_length_glue]; unfold midPos; omega),
    List.getElem?_append_left (by rw [midCode_length, reloc_length_glue]; unfold midPos; omega)]
  congr 1
  rw [reloc_length_glue]; unfold midPos; omega

lemma composite_r2 : ∀ k < rlen 0 P2, (composite e P1 P2)[base2 P1 + k]? =
    (reloc 2 0 P2 (base2 P1) (tailPos P1 P2))[k]? := by
  intro k hk
  have hb : base2 P1 = copyCode.length + rlen 1 P1 + 3 := rfl
  rw [composite_eq, List.getElem?_append_right (by omega),
    List.getElem?_append_right (by rw [reloc_length_glue]; omega),
    List.getElem?_append_right (by rw [midCode_length, reloc_length_glue]; omega),
    List.getElem?_append_left (by rw [midCode_length, reloc_length_glue, reloc_length_glue]; omega)]
  congr 1
  rw [midCode_length, reloc_length_glue]; omega

lemma composite_tail : ∀ k < 10, (composite e P1 P2)[tailPos P1 P2 + k]? =
    (tailCode e (tailPos P1 P2))[k]? := by
  intro k hk
  have hb : tailPos P1 P2 = copyCode.length + rlen 1 P1 + 3 + rlen 0 P2 := rfl
  rw [composite_eq, List.getElem?_append_right (by omega),
    List.getElem?_append_right (by rw [reloc_length_glue]; omega),
    List.getElem?_append_right (by rw [midCode_length, reloc_length_glue]; omega),
    List.getElem?_append_right (by rw [midCode_length, reloc_length_glue, reloc_length_glue]; omega)]
  congr 1
  rw [midCode_length, reloc_length_glue, reloc_length_glue]; omega

end layout

section copy

/-- loop invariant of the copy loop at pc 3 -/
def CInv (n : ℕ) (I0 : ℤ → ℤ) (x : ℤ) (St : State) : Prop :=
  St.cfg.pc = 3 ∧ St.output = none ∧ St.coins = 0 ∧ St.queries = 0 ∧ (∀ i, St.cfg.regs i = 0) ∧
  (∀ y, St.cfg.mem y = 0) ∧ St.cfg.ptrs 3 = x ∧ St.cfg.ptrs 9 = 0 ∧
  (∀ j, j % 3 ≠ 0 → St.cfg.ptrs j = 0) ∧
  ∀ y, St.imem y = if 2 * (x + 1) ≤ y ∧ y ≤ 2 * n + 1 then I0 (y / 2) else I0 y

variable (Q : Program) (hQ : ∀ k < 12, Q[k]? = copyCode[k]?) {n : ℕ} (w : Fin n → Fin n → ℝ)
  (f : ℕ → Bool)
include hQ

lemma copy_iter (I0 : ℤ → ℤ) (x : ℤ) (hx : 0 ≤ x) (hxn : x ≤ n) (St : State) (h : CInv n I0 x St) :
    CInv n I0 (x - 1) ((step Q w f)^[8] St) := by
  obtain ⟨hpc, ho, hc, hq, hr, hm, h3, h9, hp, hi⟩ := h
  have q3 : Q[3]? = some (.core (.pjle 9 3 5)) := hQ 3 (by norm_num)
  have q5 : Q[5]? = some (.integerLoad 12 3) := hQ 5 (by norm_num)
  have q6 : Q[6]? = some (.pointerAdd 15 3 3) := hQ 6 (by norm_num)
  have q7 : Q[7]? = some (.integerStore 15 12) := hQ 7 (by norm_num)
  have q8 : Q[8]? = some (.core (.pinc 15)) := hQ 8 (by norm_num)
  have q9 : Q[9]? = some (.integerStore 15 12) := hQ 9 (by norm_num)
  have q10 : Q[10]? = some (.core (.pdec 3)) := hQ 10 (by norm_num)
  have q11 : Q[11]? = some (.core (.pjle 9 9 3)) := hQ 11 (by norm_num)
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp [CInv, step, ho, hpc, q3, q5, q6, q7, q8, q9, q10, q11, RAMStep, List.getElem?_map,
    State.next, h3, h9, hx, hc, hq, hr, hm, Instr.coreOf]
  refine ⟨fun j hj => ?_, fun y => ?_⟩
  · have : j ≠ 3 ∧ j ≠ 15 ∧ j ≠ 12 := by omega
    simp [this.1, this.2.1, this.2.2, hp j hj]
  · have hx0 : St.imem x = I0 x := by rw [hi, if_neg (by omega)]
    simp only [Function.update_apply, hx0]
    rw [hi y]
    split_ifs <;> first | rfl | omega | (congr 1; omega)

lemma copy_loop (I0 : ℤ → ℤ) (St : State) (h : CInv n I0 n St) :
    ∀ k ≤ n + 1, CInv n I0 ((n : ℤ) - k) ((step Q w f)^[8 * k] St) := by
  intro k
  induction k with
  | zero => intro _; simpa using h
  | succ k ih =>
    intro hk
    rw [show 8 * (k + 1) = 8 + 8 * k by ring, Function.iterate_add_apply]
    have := copy_iter Q hQ w f I0 ((n : ℤ) - k) (by omega) (by omega) _ (ih (by omega))
    convert this using 1
    push_cast; ring

omit hQ in
lemma init_imem_out (z : ℤ) (hz : z < 0 ∨ (n : ℤ) < z) :
    (initState (Finset.univ : Finset (Fin n))).imem z = 0 := by
  simp only [initState]
  rw [if_neg (by omega), if_neg]
  rintro ⟨v, hv, -⟩
  have := v.isLt
  omega

theorem copy_run :
    let St := (step Q w f)^[8 * (n + 1) + 5] (initState (Finset.univ : Finset (Fin n)))
    St.cfg.pc = 12 ∧ St.output = none ∧ St.coins = 0 ∧ St.queries = 0 ∧
    (∀ i, St.cfg.regs i = 0) ∧ (∀ j, j % 3 ≠ 0 → St.cfg.ptrs j = 0) ∧ (∀ y, St.cfg.mem y = 0) ∧
    (∀ x : ℤ, St.imem (2 * x) = (initState (Finset.univ : Finset (Fin n))).imem x) ∧
    (∀ x : ℤ, St.imem (2 * x + 1) = (initState (Finset.univ : Finset (Fin n))).imem x) := by
  intro St
  set I0 := (initState (Finset.univ : Finset (Fin n))).imem with hI0
  have q0 : Q[0]? = some (.core (.pset 6 0)) := hQ 0 (by norm_num)
  have q1 : Q[1]? = some (.integerLoad 3 6) := hQ 1 (by norm_num)
  have q2 : Q[2]? = some (.core (.pset 9 0)) := hQ 2 (by norm_num)
  have q3 : Q[3]? = some (.core (.pjle 9 3 5)) := hQ 3 (by norm_num)
  have q4 : Q[4]? = some (.core (.pjle 9 9 12)) := hQ 4 (by norm_num)
  have hpre : CInv n I0 n ((step Q w f)^[3] (initState (Finset.univ : Finset (Fin n)))) := by
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    simp [CInv, step, q0, q1, q2, RAMStep, List.getElem?_map, State.next, Instr.coreOf,
      initState, hI0]
    refine ⟨fun j hj => ?_, fun y h1 h2 => by omega⟩
    have : j ≠ 3 ∧ j ≠ 9 := by omega
    simp [this.1, this.2]
  have hloop := copy_loop Q hQ w f I0 _ hpre (n + 1) le_rfl
  have hSt : St = (step Q w f)^[2] ((step Q w f)^[8 * (n + 1)]
      ((step Q w f)^[3] (initState (Finset.univ : Finset (Fin n))))) := by
    simp only [St, ← Function.iterate_add_apply]
    rw [show 2 + (8 * (n + 1) + 3) = 8 * (n + 1) + 5 by ring]
  rw [hSt]
  generalize (step Q w f)^[8 * (n + 1)]
      ((step Q w f)^[3] (initState (Finset.univ : Finset (Fin n)))) = S at hloop ⊢
  obtain ⟨hpc, ho, hc, hq, hr, hm, h3, h9, hp, hi⟩ := hloop
  push_cast at h3 hi
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp [step, ho, hpc, q3, q4, RAMStep, List.getElem?_map, h3, h9, hc, hq, hr, hm,
    Instr.coreOf]
  have hout : ∀ z, z < 0 ∨ (n : ℤ) < z → I0 z = 0 := init_imem_out
  refine ⟨hp, fun x => ?_, fun x => ?_⟩
  · rw [hi]
    split_ifs with hh
    · congr 1; omega
    · rw [hout (2 * x) (by omega), hout x (by omega)]
  · rw [hi]
    split_ifs with hh
    · congr 1; omega
    · rw [hout (2 * x + 1) (by omega), hout x (by omega)]

end copy

section midtail

theorem mid_run (Q : Program) (m : ℕ) (hQ : ∀ k < 3, Q[m + k]? = midCode[k]?) {n : ℕ}
    (w : Fin n → Fin n → ℝ) (f : ℕ → Bool) (St : State)
    (hpc : St.cfg.pc = m) (hout : St.output = none) (hZR : St.cfg.regs ZR = 0) :
    let St' := (step Q w f)^[3] St
    St'.cfg.pc = m + 3 ∧ St'.output = none ∧ St'.coins = St.coins ∧ St'.queries = St.queries ∧
    St'.cfg.mem 0 = St.cfg.regs OUT ∧ (∀ y, y ≠ 0 → St'.cfg.mem y = St.cfg.mem y) ∧
    St'.cfg.regs 6 = St.cfg.regs OUT ∧ (∀ i, i ≠ 6 → St'.cfg.regs i = St.cfg.regs i) ∧
    (∀ j, j ≠ 3 → St'.cfg.ptrs j = St.cfg.ptrs j) ∧ St'.imem = St.imem := by
  intro St'
  have q0 : Q[m]? = some (.core (.pset 3 0)) := by simpa [midCode] using hQ 0 (by norm_num)
  have q1 : Q[m + 1]? = some (.core (.store 3 OUT)) := hQ 1 (by norm_num)
  have q2 : Q[m + 2]? = some (.core (.add 6 OUT ZR)) := hQ 2 (by norm_num)
  simp only [OUT, ZR] at q1 q2 hZR ⊢
  simp only [St', Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp [step, hout, hpc, q0, q1, q2, RAMStep, List.getElem?_map, Instr.coreOf, hZR]
  refine ⟨?_, ?_, ?_⟩ <;> intro a ha <;> simp [ha]

theorem tail_run (Q : Program) (e : ℚ) (t0 : ℕ) (hQ : ∀ k < 10, Q[t0 + k]? = (tailCode e t0)[k]?)
    {n : ℕ} (w : Fin n → Fin n → ℝ) (f : ℕ → Bool) (St : State)
    (hpc : St.cfg.pc = t0) (hout : St.output = none) :
    ((step Q w f)^[7] St).output =
      some (if ((1 + e : ℚ) : ℝ) * St.cfg.regs 6 / 2 ≤ St.cfg.regs OUT then 2 * St.cfg.regs 6
            else ((2 - e : ℚ) : ℝ) * St.cfg.regs 6) ∧
    ((step Q w f)^[7] St).queries = St.queries := by
  have q0 : Q[t0]? = some (.core (.const 9 (((1 + e) / 2 : ℚ) : ℝ))) := by
    simpa [tailCode] using hQ 0 (by norm_num)
  have q1 : Q[t0 + 1]? = some (.core (.mul 12 9 6)) := by simpa [tailCode] using hQ 1 (by norm_num)
  have q2 : Q[t0 + 2]? = some (.core (.sub 12 12 OUT)) := by
    simpa [tailCode] using hQ 2 (by norm_num)
  have q3 : Q[t0 + 3]? = some (.core (.jle 12 (t0 + 7))) := by
    simpa [tailCode] using hQ 3 (by norm_num)
  have q4 : Q[t0 + 4]? = some (.core (.const 15 (((2 - e) : ℚ) : ℝ))) := by
    simpa [tailCode] using hQ 4 (by norm_num)
  have q5 : Q[t0 + 5]? = some (.core (.mul 18 15 6)) := by simpa [tailCode] using hQ 5 (by norm_num)
  have q6 : Q[t0 + 6]? = some (.halt 18) := by simpa [tailCode] using hQ 6 (by norm_num)
  have q7 : Q[t0 + 7]? = some (.core (.const 15 ((2 : ℚ) : ℝ))) := by
    simpa [tailCode] using hQ 7 (by norm_num)
  have q8 : Q[t0 + 8]? = some (.core (.mul 18 15 6)) := by simpa [tailCode] using hQ 8 (by norm_num)
  have q9 : Q[t0 + 9]? = some (.halt 18) := by simpa [tailCode] using hQ 9 (by norm_num)
  simp only [OUT] at q2 ⊢
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  by_cases hc : (1 + (e : ℝ)) / 2 * St.cfg.regs 6 ≤ St.cfg.regs 3
  · simp [step, hout, hpc, q0, q1, q2, q3, q7, q8, q9, RAMStep, List.getElem?_map, Instr.coreOf,
      hc]
    intro h; exfalso; linarith
  · simp [step, hout, hpc, q0, q1, q2, q3, q4, q5, q6, RAMStep, List.getElem?_map, Instr.coreOf,
      hc]
    intro h; exact absurd (by linarith) hc

end midtail
end MTSPComp

end

section

open scoped Classical

namespace MTSPMstFinal
open SublinearSteiner MTSPEst Finset

lemma mst_small {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (hn : n ≤ 1) :
    DoublingMST.mstWeight d = 0 := by
  rcases Nat.lt_or_ge n 1 with h0 | h1
  · have hn0 : n = 0 := by omega
    subst hn0
    unfold DoublingMST.mstWeight
    have hS : {w : ℝ | ∃ T : Finset (Sym2 (Fin 0)), (DoublingMST.completeGraph 0).IsSpanningTree T ∧
        DoublingMST.treeWeight d T = w} ⊆ {0} := by
      rintro w ⟨T, -, rfl⟩
      have : T = ∅ := Finset.eq_empty_of_forall_notMem (fun e => by
        induction e with | _ a b => exact a.elim0)
      subst this; simp [DoublingMST.treeWeight]
    rcases Set.subset_singleton_iff_eq.mp hS with h | h
    · rw [h, Real.sInf_empty]
    · rw [h, csInf_singleton]
  · have hn1 : n = 1 := by omega
    subst hn1
    rw [MTSPMst.mst_eq_prim d hd ⟨0, by omega⟩]
    simp [MTSPMst.grun]

lemma q_bound (n : ℕ) : ((qOf n : ℝ) + 1) ^ 3 * ((n : ℝ) + 1) ≤ 27 * ((n : ℝ) + 1) ^ ((2 : ℝ) - 1 / 4) := by
  set y := ((n : ℝ) + 1) ^ ((1 : ℝ) / 4) with hy
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hy1 : 1 ≤ y := Real.one_le_rpow hn1 (by norm_num)
  have hy4 : y ^ 4 = (n : ℝ) + 1 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hy7 : y ^ 7 = ((n : ℝ) + 1) ^ ((2 : ℝ) - 1 / 4) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hq : (qOf n : ℝ) + 1 ≤ 3 * y := by
    by_cases h : qOf n ≤ 1
    · have : (qOf n : ℝ) ≤ 1 := by exact_mod_cast h
      linarith
    · have hlt := qOf_min n (qOf n - 1) (by omega) (by omega)
      have hlt' : ((qOf n - 1 : ℕ) : ℝ) ^ 4 < y ^ 4 := by
        rw [hy4]; have : ((qOf n - 1 : ℕ) : ℝ) ^ 4 < (n : ℝ) := by exact_mod_cast hlt
        linarith
      have h2 : ((qOf n - 1 : ℕ) : ℝ) < y :=
        lt_of_pow_lt_pow_left₀ 4 (by linarith) hlt'
      have h3 : ((qOf n - 1 : ℕ) : ℝ) = (qOf n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [h3] at h2; linarith
  rw [← hy7, ← hy4]
  have h0 : 0 ≤ (qOf n : ℝ) + 1 := by positivity
  calc ((qOf n : ℝ) + 1) ^ 3 * y ^ 4 ≤ (3 * y) ^ 3 * y ^ 4 := by gcongr
    _ = 27 * y ^ 7 := by ring

lemma fac_ineq (c η : ℝ) (hc : 0 ≤ c) (hc3 : 15 * c ≤ 1) (hη : 15 * c ≤ η) :
    1 + 5 * c ≤ (1 + η) * (1 - 5 * c) := by nlinarith

theorem final :
    ∀ η : ℝ, 0 < η → ∃ (ε γ : ℝ) (P : SublinearSteiner.Program) (C : ℝ), 0 < ε ∧ 0 < γ ∧
      SublinearSteiner.Admissible P ∧
      ∀ (n : ℕ) (d : Fin n → Fin n → ℝ), DoublingMST.IsMetric d →
        (∀ tape : Fin ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ → Bool,
            (SublinearSteiner.run P Finset.univ d tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).output.isSome ∧
            ((SublinearSteiner.run P Finset.univ d tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).queries : ℝ) ≤
              C * ((n : ℝ) + 1) ^ (2 - ε)) ∧
        (5 / 6 : ℝ) * 2 ^ ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ ≤
          ((Finset.univ.filter (fun tape : Fin ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ → Bool => ∃ z : ℝ,
              (SublinearSteiner.run P Finset.univ d tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).output = some z ∧
              DoublingMST.mstWeight d ≤ z ∧ z ≤ (1 + η) * DoublingMST.mstWeight d)).card : ℝ) := by
  intro η hη
  obtain ⟨e, he0, he1⟩ := exists_rat_btwn (show (0 : ℝ) < min η 1 / 15 by positivity)
  have he0' : (0 : ℝ) < e := by exact_mod_cast he0
  have hemin : (e : ℝ) ≤ min η 1 / 15 := he1.le
  have heη : 15 * (e : ℝ) ≤ η := by have := min_le_left η 1; linarith
  have he1' : 15 * (e : ℝ) ≤ 1 := by have := min_le_right η 1; linarith
  have heq : 0 < e := by exact_mod_cast he0'
  have heq1 : e ≤ 1 := by exact_mod_cast (show (e : ℝ) ≤ 1 by linarith)
  set S1 : ℕ := ⌈(2 : ℝ) / (e : ℝ) ^ 2⌉₊ + 1 with hS1
  set R1 : ℕ := ⌈(192 : ℝ) / (e : ℝ) ^ 4⌉₊ + 1 with hR1
  set scale : ℚ := 1 / (1 - 5 * e) with hscale
  set Pg := estProg 1 S1 R1 (1 / e) scale with hPg
  set C : ℝ := 28 * ((estC 1 S1 R1 : ℝ) + estQ 1 S1 R1 + R1) with hC
  refine ⟨1 / 4, 1 / 4, Pg, C, by norm_num, by norm_num, estProg_adm _ _ _ _ _, ?_⟩
  intro n d hd
  set B := ⌈C * ((n : ℝ) + 1) ^ ((2 : ℝ) - 1 / 4)⌉₊ with hB
  set x := ((n : ℝ) + 1) ^ ((2 : ℝ) - 1 / 4) with hx
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hx1 : 1 ≤ x := Real.one_le_rpow hn1 (by norm_num)
  have hqb := q_bound n
  rw [← hx] at hqb
  have hBge : C * x ≤ (B : ℝ) := Nat.le_ceil _
  have hTB : ∀ T ≤ timeBound 1 S1 R1 n, T ≤ B := by
    intro T hT
    have : (T : ℝ) ≤ B := by
      refine le_trans ?_ hBge
      have h1 : (T : ℝ) ≤ timeBound 1 S1 R1 n := by exact_mod_cast hT
      simp only [timeBound] at h1; push_cast at h1
      have hc0 : (0 : ℝ) ≤ estC 1 S1 R1 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hqb hc0]
    exact_mod_cast this
  have hrm : rOf R1 n * mOf n ≤ B := by
    have : ((rOf R1 n * mOf n : ℕ) : ℝ) ≤ B := by
      refine le_trans ?_ hBge
      have hm : (mOf n : ℝ) ≤ n := by exact_mod_cast mOf_le n
      have hq : (qOf n : ℝ) ^ 2 ≤ ((qOf n : ℝ) + 1) ^ 3 := by
        have : (1 : ℝ) ≤ (qOf n : ℝ) + 1 := by linarith [(Nat.cast_nonneg (qOf n) : (0 : ℝ) ≤ qOf n)]
        nlinarith [sq_nonneg ((qOf n : ℝ) + 1), (Nat.cast_nonneg (qOf n) : (0 : ℝ) ≤ qOf n)]
      simp only [rOf]; push_cast
      have hR0 : (0 : ℝ) ≤ R1 := by positivity
      have h1 : (R1 : ℝ) * (qOf n : ℝ) ^ 2 * (mOf n : ℝ) ≤ R1 * (((qOf n : ℝ) + 1) ^ 3 * ((n : ℝ) + 1)) := by
        have := mul_le_mul hq (show (mOf n : ℝ) ≤ (n : ℝ) + 1 by linarith) (by positivity) (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left this hR0]
      have h2 := mul_le_mul_of_nonneg_left hqb hR0
      have : (0 : ℝ) ≤ estC 1 S1 R1 + estQ 1 S1 R1 := by positivity
      nlinarith
    exact_mod_cast this
  -- the run on a tape
  have hrun : ∀ t : Fin B → Bool,
      (run Pg Finset.univ d t B).output = some (estOut 1 S1 R1 (1 / e) scale d (MTSPDecode.dec (mOf n) (extendTape t))) ∧
      (run Pg Finset.univ d t B).queries ≤ queryBound 1 S1 R1 n := by
    intro t
    obtain ⟨T, hT, hout, hq, -⟩ := est_run 1 S1 R1 (1 / e) scale le_rfl d hd (extendTape t)
    have hTB' := hTB T hT
    have key : (step Pg d (extendTape t))^[B] (initState (Finset.univ : Finset (Fin n))) =
        (step Pg d (extendTape t))^[T] (initState (Finset.univ : Finset (Fin n))) := by
      have h := Function.iterate_add_apply (step Pg d (extendTape t)) (B - T) T
        (initState (Finset.univ : Finset (Fin n)))
      rw [Nat.sub_add_cancel hTB'] at h
      rw [h, MTSPComp.iterate_halted _ _ _ _ _ hout]
    unfold run; rw [key]; exact ⟨hout, hq⟩
  refine ⟨fun t => ?_, ?_⟩
  · obtain ⟨ho, hq⟩ := hrun t
    refine ⟨by rw [ho]; rfl, ?_⟩
    refine le_trans (Nat.cast_le.mpr hq) ?_
    have : (queryBound 1 S1 R1 n : ℝ) ≤ C * x := by
      simp only [queryBound]; push_cast
      have hc0 : (0 : ℝ) ≤ estQ 1 S1 R1 := by positivity
      have := mul_le_mul_of_nonneg_left hqb hc0
      have : (0 : ℝ) ≤ estC 1 S1 R1 + R1 := by positivity
      nlinarith
    simpa [hx] using this
  · set M := DoublingMST.mstWeight d with hM
    -- the good set
    let G : (ℕ → ℕ) → Prop := fun v =>
      M ≤ estOut 1 S1 R1 (1 / e) scale d v ∧ estOut 1 S1 R1 (1 / e) scale d v ≤ (1 + η) * M
    have hsub : (Finset.univ.filter (fun t : Fin B → Bool => G (MTSPDecode.dec (mOf n) (extendTape t)))) ⊆
        (Finset.univ.filter (fun tape : Fin B → Bool => ∃ z : ℝ,
          (run Pg Finset.univ d tape B).output = some z ∧ M ≤ z ∧ z ≤ (1 + η) * M)) := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact ⟨_, (hrun t).1, ht⟩
    refine le_trans ?_ (Nat.cast_le.mpr (Finset.card_le_card hsub))
    have hG : ∀ v v' : ℕ → ℕ, (∀ i < rOf R1 n, v i = v' i) → (G v ↔ G v') := by
      intro v v' hv
      have : estOut 1 S1 R1 (1 / e) scale d v = estOut 1 S1 R1 (1 / e) scale d v' := by
        unfold estOut
        split_ifs
        · rfl
        · rw [Finset.sum_congr rfl (fun i hi => by rw [hv i (Finset.mem_range.mp hi)])]
      simp only [G, this]
    have htc := MTSPDecode.tape_count (rOf R1 n) (mOf n) B hrm G hG
    suffices h : (5 / 6 : ℝ) * 2 ^ B ≤ 2 ^ (B - rOf R1 n * mOf n) *
        ((Finset.univ.filter (fun u : Fin (rOf R1 n) → Fin (2 ^ mOf n) =>
          G (fun i => if h : i < rOf R1 n then (u ⟨i, h⟩ : ℕ) else 0))).card : ℝ) by
      refine le_of_le_of_eq h ?_
      convert htc.symm using 2
      all_goals first | rfl | (ext x; simp) | (congr 1; ext x; simp) | (congr 2; ext x; simp) | (congr 3; ext x; simp)
    by_cases hn : n ≤ 1
    · have hM0 : M = 0 := mst_small d hd hn
      have hall : (Finset.univ.filter (fun u : Fin (rOf R1 n) → Fin (2 ^ mOf n) =>
          G (fun i => if h : i < rOf R1 n then (u ⟨i, h⟩ : ℕ) else 0))) = Finset.univ := by
        apply Finset.filter_true_of_mem
        intro u _
        simp only [G, estOut, dif_pos hn, hM0, mul_zero, le_refl, and_self]
      rw [hall, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      push_cast
      rw [← pow_mul, ← pow_add, show B - rOf R1 n * mOf n + mOf n * rOf R1 n = B by
        rw [show mOf n * rOf R1 n = rOf R1 n * mOf n from Nat.mul_comm _ _]; exact Nat.sub_add_cancel hrm]
      have : (0 : ℝ) ≤ 2 ^ B := by positivity
      linarith
    · have hn2 : 2 ≤ n := by omega
      have hS1r : (2 : ℝ) / (e : ℝ) ^ 2 ≤ S1 := by
        simp only [hS1]; push_cast; linarith [Nat.le_ceil ((2 : ℝ) / (e : ℝ) ^ 2)]
      have hR1r : (192 : ℝ) / (e : ℝ) ^ 4 ≤ R1 := by
        simp only [hR1]; push_cast; linarith [Nat.le_ceil ((192 : ℝ) / (e : ℝ) ^ 4)]
      have hgood := MTSPGlue.est_good S1 R1 e heq heq1 hS1r hR1r (by omega) (by omega) d hd hn2
      have hM0 : 0 ≤ M := by
        have := (MTSPGlue.vals_nonneg hd false (fun _ => true) ⟨0, by omega⟩ (n - 1))
        rw [hM, MTSPMst.mst_eq_prim d hd ⟨0, by omega⟩]
        apply List.sum_nonneg
        intro w hw
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
        exact this p hp
      have himp : (Finset.univ.filter (fun u : Fin (rOf R1 n) → Fin (2 ^ mOf n) =>
            |A' 1 (1 / e) d (by omega) + ((2 ^ mOf n : ℕ) / (rOf R1 n) : ℝ) *
              ∑ i, X 1 S1 (1 / e) d (by omega) (u i) - T1 1 (1 / e) d (by omega) - M| ≤ 5 * (e : ℝ) * M)) ⊆
          (Finset.univ.filter (fun u : Fin (rOf R1 n) → Fin (2 ^ mOf n) =>
            G (fun i => if h : i < rOf R1 n then (u ⟨i, h⟩ : ℕ) else 0))) := by
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        set E := A' 1 (1 / e) d (by omega) + ((2 ^ mOf n : ℕ) / (rOf R1 n) : ℝ) *
              ∑ i, X 1 S1 (1 / e) d (by omega) (u i) - T1 1 (1 / e) d (by omega) with hE
        have hout : estOut 1 S1 R1 (1 / e) scale d (fun i => if h : i < rOf R1 n then (u ⟨i, h⟩ : ℕ) else 0)
            = E * (1 / (1 - 5 * (e : ℝ))) := by
          have hsum : ∑ i ∈ range (rOf R1 n), X 1 S1 (1 / e) d (by omega)
              (if h : i < rOf R1 n then (u ⟨i, h⟩ : ℕ) else 0) = ∑ i, X 1 S1 (1 / e) d (by omega) (u i) := by
            rw [Finset.sum_range (fun i => X 1 S1 (1 / e) d (by omega)
              (if h : i < rOf R1 n then (u ⟨i, h⟩ : ℕ) else 0))]
            apply Finset.sum_congr rfl
            intro i _
            rw [dif_pos i.isLt]
          unfold estOut
          rw [dif_neg hn, hE, hsum, hscale]
          push_cast
          ring
        show M ≤ _ ∧ _ ≤ (1 + η) * M
        rw [hout]
        have hc : 5 * (e : ℝ) ≤ 1 / 3 := by linarith
        have hden : 0 < 1 - 5 * (e : ℝ) := by linarith
        obtain ⟨h1, h2⟩ := abs_le.mp hu
        constructor
        · rw [mul_one_div, le_div_iff₀ hden]
          have := mul_le_mul_of_nonneg_left (le_refl (5 * (e : ℝ))) hM0
          linarith
        · rw [mul_one_div, div_le_iff₀ hden]
          have hfac := fac_ineq (e : ℝ) η he0'.le (by linarith) (by linarith)
          have := mul_le_mul_of_nonneg_left hfac hM0
          linarith
      have hcard := le_trans hgood (Nat.cast_le.mpr (Finset.card_le_card himp))
      have hpow : (2 : ℝ) ^ (B - rOf R1 n * mOf n) * ((2 ^ mOf n : ℕ) : ℝ) ^ (rOf R1 n) = 2 ^ B := by
        push_cast
        rw [← pow_mul, ← pow_add, show B - rOf R1 n * mOf n + mOf n * rOf R1 n = B by
          rw [show mOf n * rOf R1 n = rOf R1 n * mOf n from Nat.mul_comm _ _]; exact Nat.sub_add_cancel hrm]
      have h2B : (0 : ℝ) ≤ 2 ^ (B - rOf R1 n * mOf n) := by positivity
      have hB0 : (0 : ℝ) ≤ 2 ^ B := by positivity
      calc (5 / 6 : ℝ) * 2 ^ B ≤ 11 / 12 * 2 ^ B := by linarith
        _ = 2 ^ (B - rOf R1 n * mOf n) * (11 / 12 * ((2 ^ mOf n : ℕ) : ℝ) ^ (rOf R1 n)) := by
          rw [← hpow]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hcard h2B

end MTSPMstFinal

end

section
open scoped Classical
open MetricTSPSublinear

theorem solution :
    ∀ η : ℝ, 0 < η → ∃ (ε γ : ℝ) (P : SublinearSteiner.Program) (C : ℝ), 0 < ε ∧ 0 < γ ∧
      SublinearSteiner.Admissible P ∧
      ∀ (n : ℕ) (d : Fin n → Fin n → ℝ), DoublingMST.IsMetric d →
        (∀ tape : Fin ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ → Bool,
            (SublinearSteiner.run P Finset.univ d tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).output.isSome ∧
            ((SublinearSteiner.run P Finset.univ d tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).queries : ℝ) ≤
              C * ((n : ℝ) + 1) ^ (2 - ε)) ∧
        (5 / 6 : ℝ) * 2 ^ ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ ≤
          ((Finset.univ.filter (fun tape : Fin ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ → Bool => ∃ z : ℝ,
              (SublinearSteiner.run P Finset.univ d tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).output = some z ∧
              DoublingMST.mstWeight d ≤ z ∧ z ≤ (1 + η) * DoublingMST.mstWeight d)).card : ℝ) :=
  MTSPMstFinal.final

end