-- Prove2me | solution 1 for MetricTSPSublinear.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:08:01.91342+00:00
-- url     : https://prove2.me/submissions/eb7a20a1-1909-40ed-a902-3cc7f59db31a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SublinearSteiner_Machine
import Mathlib
import Definitions.Def_MetricTSPSublinear_runWithEstimate
import Theorems.Thm_MetricTSPSublinear_mst_estimator_program
import Theorems.Thm_MetricTSPSublinear_lemma_9_1_timed
import Theorems.Thm_MetricTSPSublinear_theorem_1_decision_rule
import Theorems.Thm_MetricTSPSublinear_claim_3_3
import Theorems.Thm_MetricTSPSublinear_claim_3_2


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



namespace MTSPComp
open SublinearSteiner SmaleNinth

/-! ### Lengths and positions -/

lemma rs_addrCode_length (b q q' : ℕ) : (addrCode b q).length = (addrCode b q').length := by
  unfold addrCode; split_ifs <;> simp

lemma rs_block_length (s b : ℕ) (pos : ℕ → ℕ) (cont : ℕ) (i : Instr) :
    (block s b pos cont i).length = blen b i := by
  cases i with
  | core ci => cases ci <;> simp [block, blen, rs_addrCode_length b _ 0]
  | _ => simp [block, blen, rs_addrCode_length b _ 0]

lemma reloc_length (s b : ℕ) (P : Program) (base cont : ℕ) :
    (reloc s b P base cont).length = rlen b P := by
  simp [reloc, rlen, List.length_flatten, Function.comp_def, rs_block_length]

lemma posOf_succ (b : ℕ) (P : Program) (base k : ℕ) (hk : k < P.length) :
    posOf b P base (k + 1) = posOf b P base k + blen b P[k] := by
  unfold posOf
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

lemma flatten_getElem? {α : Type*} (ls : List (List α)) (k m : ℕ) (hk : k < ls.length)
    (hm : m < ls[k].length) :
    ls.flatten[((ls.take k).map List.length).sum + m]? = ls[k][m]? := by
  induction ls generalizing k with
  | nil => simp at hk
  | cons l ls ih =>
    cases k with
    | zero =>
      simp only [List.flatten_cons, List.take_zero, List.map_nil, List.sum_nil, zero_add]
      rw [List.getElem?_append_left (by simpa using hm)]
      simp
    | succ k =>
      simp only [List.flatten_cons, List.take_succ_cons, List.map_cons, List.sum_cons]
      rw [List.getElem?_append_right (by omega)]
      have := ih k (by simpa using hk) (by simpa using hm)
      simp only [List.getElem_cons_succ] at this ⊢
      rw [← this]; congr 1; omega

lemma reloc_getElem? (s b : ℕ) (P : Program) (base cont k m : ℕ) (hk : k < P.length)
    (hm : m < blen b P[k]) :
    (reloc s b P base cont)[((P.take k).map (blen b)).sum + m]? =
      (block s b (posOf b P base) cont P[k])[m]? := by
  have h := flatten_getElem? (P.map (block s b (posOf b P base) cont)) k m (by simpa using hk)
    (by simpa [rs_block_length] using hm)
  simp only [List.getElem_map] at h
  rw [← h, reloc]
  congr 2
  rw [← List.map_take, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _; simp [rs_block_length]

lemma take_sum_lt (b : ℕ) (P : Program) (k m : ℕ) (hk : k < P.length) (hm : m < blen b P[k]) :
    ((P.take k).map (blen b)).sum + m < rlen b P := by
  have h1 := List.sum_take_add_sum_drop (P.map (blen b)) (k + 1)
  have h2 : ((P.take (k+1)).map (blen b)).sum = ((P.take k).map (blen b)).sum + blen b P[k] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk]
    simp only [Option.toList_some, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
  rw [← List.map_take] at h1
  unfold rlen; omega


/-! ### Correspondence and frame -/

/-- Correspondence between a state `σ` of `P` and a state `τ` of a program containing the
relocated `P`. (`Σ` is a reserved token in Lean 4, hence `St`.) -/
structure Corr (P : Program) (s b base c0 q0 : ℕ) (σ St : State) : Prop where
  pc : St.cfg.pc = posOf b P base σ.cfg.pc
  regs : ∀ i, St.cfg.regs (rr s i) = σ.cfg.regs i
  ptrs : ∀ j, St.cfg.ptrs (rr s j) = σ.cfg.ptrs j
  mem : ∀ x : ℤ, St.cfg.mem (2 * x + b) = σ.cfg.mem x
  imem : ∀ x : ℤ, St.imem (2 * x + b) = σ.imem x
  coins : St.coins = c0 + σ.coins
  queries : St.queries = q0 + σ.queries
  outSt : St.output = none

/-- What a relocated block leaves untouched. -/
structure Frame (s b : ℕ) (τ τ' : State) : Prop where
  regs : ∀ i, i % 3 ≠ s → i ≠ OUT → τ'.cfg.regs i = τ.cfg.regs i
  ptrs : ∀ j, j % 3 ≠ s → j ≠ S0 → τ'.cfg.ptrs j = τ.cfg.ptrs j
  mem : ∀ y : ℤ, y % 2 ≠ (b : ℤ) → τ'.cfg.mem y = τ.cfg.mem y
  imem : ∀ y : ℤ, y % 2 ≠ (b : ℤ) → τ'.imem y = τ.imem y

lemma Frame.refl (s b : ℕ) (τ : State) : Frame s b τ τ :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

lemma Frame.trans {s b : ℕ} {τ1 τ2 τ3 : State} (h1 : Frame s b τ1 τ2) (h2 : Frame s b τ2 τ3) :
    Frame s b τ1 τ3 :=
  ⟨fun i hi ho => (h2.regs i hi ho).trans (h1.regs i hi ho),
   fun j hj ho => (h2.ptrs j hj ho).trans (h1.ptrs j hj ho),
   fun y hy => (h2.mem y hy).trans (h1.mem y hy),
   fun y hy => (h2.imem y hy).trans (h1.imem y hy)⟩

@[simp] lemma rr_inj (s i j : ℕ) : rr s i = rr s j ↔ i = j := by
  unfold rr; omega

lemma ne_rr {s : ℕ} (hs : s = 1 ∨ s = 2) {i : ℕ} (hi : i % 3 ≠ s) (d : ℕ) : i ≠ rr s d := by
  unfold rr; omega

lemma rr_ne_S0 {s : ℕ} (hs : s = 1 ∨ s = 2) (d : ℕ) : rr s d ≠ S0 := by
  unfold rr S0; omega

@[simp] lemma two_mul_add_inj (x y : ℤ) (b : ℕ) : 2 * x + (b : ℤ) = 2 * y + b ↔ x = y := by
  omega

lemma ne_par {b : ℕ} (hb : b = 0 ∨ b = 1) {y : ℤ} (hy : y % 2 ≠ (b : ℤ)) (x : ℤ) :
    y ≠ 2 * x + b := by
  rcases hb with rfl | rfl <;> omega

/-! ### Basic facts about `step` -/

section steps
variable {n : ℕ} (w : Fin n → Fin n → ℝ) (tape : ℕ → Bool)

lemma rs_step_halted (P : Program) (σ : State) {z : ℝ} (h : σ.output = some z) :
    step P w tape σ = σ := by
  simp [step, h]

lemma rs_iterate_halted (P : Program) (σ : State) {z : ℝ} (h : σ.output = some z) (k : ℕ) :
    (step P w tape)^[k] σ = σ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, rs_step_halted w tape P σ h]

/-- A stuck state: no output, and the pc carries no instruction or `accept`/`reject`. -/
def Stuck (P : Program) (σ : State) : Prop :=
  σ.output = none ∧ (P[σ.cfg.pc]? = none ∨ P[σ.cfg.pc]? = some (.core .accept) ∨
    P[σ.cfg.pc]? = some (.core .reject))

lemma stuck_step (P : Program) (σ : State) (h : Stuck P σ) : Stuck P (step P w tape σ) := by
  obtain ⟨h0, h1 | h1 | h1⟩ := h
  · refine ⟨?_, Or.inl ?_⟩ <;> simp [step, h0, h1]
  · have : (P.map Instr.coreOf)[σ.cfg.pc]? = some .accept := by simp [h1, Instr.coreOf]
    refine ⟨?_, Or.inr (Or.inl ?_)⟩ <;> simp [step, h0, h1, RAMStep, this]
  · have : (P.map Instr.coreOf)[σ.cfg.pc]? = some .reject := by simp [h1, Instr.coreOf]
    refine ⟨?_, Or.inr (Or.inr ?_)⟩ <;> simp [step, h0, h1, RAMStep, this]

lemma stuck_iterate (P : Program) (σ : State) (h : Stuck P σ) (k : ℕ) :
    Stuck P ((step P w tape)^[k] σ) := by
  induction k with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply']; exact stuck_step w tape P _ ih

lemma step_output_none (P : Program) (σ : State) (i : Instr) (h0 : σ.output = none)
    (hp : P[σ.cfg.pc]? = some i) (hh : ∀ src, i ≠ .halt src) :
    (step P w tape σ).output = none := by
  cases i with
  | halt src => exact absurd rfl (hh src)
  | core ci => simp [step, h0, hp]
  | _ => simp [step, h0, hp, State.next]

lemma step_halt (P : Program) (σ : State) (src : ℕ) (h0 : σ.output = none)
    (hp : P[σ.cfg.pc]? = some (.halt src)) :
    step P w tape σ = { σ with output := some (σ.cfg.regs src), work := σ.work + 1 } := by
  simp [step, h0, hp]

end steps


lemma Qat {P Q : Program} {s b base cont c0 q0 : ℕ}
    (hQ : ∀ k < rlen b P, Q[base + k]? = (reloc s b P base cont)[k]?)
    {σ St : State} (hc : Corr P s b base c0 q0 σ St) (hk : σ.cfg.pc < P.length)
    (m : ℕ) (hm : m < blen b P[σ.cfg.pc]) :
    Q[St.cfg.pc + m]? = (block s b (posOf b P base) cont P[σ.cfg.pc])[m]? := by
  rw [hc.pc, posOf, add_assoc, hQ _ (take_sum_lt b P _ m hk hm), reloc_getElem? s b P base cont _ m hk hm]

lemma addr_run (Q : Program) {n : ℕ} (w : Fin n → Fin n → ℝ) (tape : ℕ → Bool) (St : State)
    (b q : ℕ) (hb : b = 0 ∨ b = 1) (h0 : St.output = none)
    (hq : ∀ m < (addrCode b q).length, Q[St.cfg.pc + m]? = (addrCode b q)[m]?) :
    (step Q w tape)^[(addrCode b q).length] St =
      { St with
        cfg := ⟨St.cfg.pc + (addrCode b q).length, St.cfg.regs,
          Function.update St.cfg.ptrs S0 (2 * St.cfg.ptrs q + b), St.cfg.mem⟩
        work := St.work + (addrCode b q).length } := by
  rcases hb with rfl | rfl
  · have h := hq 0 (by simp [addrCode])
    simp [addrCode] at h
    simp [addrCode, step, h0, h, State.next, two_mul]
  · have h := hq 0 (by simp [addrCode])
    have h' := hq 1 (by simp [addrCode])
    simp [addrCode] at h h'
    have h'' : (Q.map Instr.coreOf)[St.cfg.pc + 1]? = some (.pinc S0) := by
      simp [h', Instr.coreOf]
    simp [addrCode, step, h0, h, h', h'', State.next, RAMStep, two_mul, add_assoc]




theorem sim_one {P Q : Program} {s b base cont c0 q0 : ℕ} (hs : s = 1 ∨ s = 2)
    (hb : b = 0 ∨ b = 1)
    (hQ : ∀ k < rlen b P, Q[base + k]? = (reloc s b P base cont)[k]?)
    {n : ℕ} (w : Fin n → Fin n → ℝ) (f : ℕ → Bool) {σ St : State} {ins : Instr}
    (h0 : σ.output = none) (hp : P[σ.cfg.pc]? = some ins) (ha : ins ≠ .core .accept)
    (hr : ins ≠ .core .reject) (hh : ∀ src, ins ≠ .halt src)
    (hc : Corr P s b base c0 q0 σ St) :
    ∃ m ≤ 3, Corr P s b base c0 q0 (step P w (fun j => f (c0 + j)) σ) ((step Q w f)^[m] St) ∧
      Frame s b St ((step Q w f)^[m] St) := by
  obtain ⟨hk, hPk⟩ := List.getElem?_eq_some_iff.mp hp
  have hQat : ∀ m < blen b ins, Q[St.cfg.pc + m]? = (block s b (posOf b P base) cont ins)[m]? := by
    intro m hm; rw [Qat hQ hc hk m (by rwa [hPk]), hPk]
  have hpos : posOf b P base (σ.cfg.pc + 1) = St.cfg.pc + blen b ins := by
    rw [posOf_succ _ _ _ _ hk, hPk, hc.pc]
  obtain ⟨cpc, cregs, cptrs, cmem, cimem, ccoins, cqueries, hO⟩ := hc
  clear hQ
  cases ins with
  | core ci =>
    cases ci with
    | load d qq =>
      simp only [blen, block] at hpos hQat
      rw [rs_addrCode_length b 0 (rr s qq)] at hpos hQat
      have hA := addr_run Q w f St b (rr s qq) hb hO (fun m hm => by
        rw [hQat m (by omega)]; simp [List.getElem?_append_left hm])
      have e0 := hQat _ (Nat.lt_succ_self _)
      simp only [List.getElem?_concat_length] at e0
      have hL2 : (addrCode b (rr s qq)).length ≤ 2 := by unfold addrCode; split_ifs <;> simp
      generalize (addrCode b (rr s qq)).length = L at hA e0 hpos hL2
      refine ⟨L + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply', hA]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals try simp [step, h0, hO, hp, e0, rr_ne_S0 hs, Instr.coreOf, RAMStep, State.next, hpos,
        Function.update_apply, cregs, cptrs, cmem, cimem, ccoins, cqueries, add_assoc,
        apply_ite RAMConfig.pc, apply_ite RAMConfig.regs, apply_ite RAMConfig.ptrs,
        apply_ite RAMConfig.mem, apply_ite (posOf b P base)]
      all_goals try refine ⟨fun i hi _ => ?_, fun j hj hS => ?_, fun y hy => ?_, fun y hy => ?_⟩
      all_goals try (have hne := ne_rr hs hi; simp [step, h0, hO, e0, Instr.coreOf, RAMStep, State.next,
        apply_ite RAMConfig.regs,
        Function.update_apply, hne])
      all_goals try (have hne := ne_rr hs hj; simp [step, h0, hO, e0, Instr.coreOf, RAMStep, State.next,
        apply_ite RAMConfig.ptrs,
        Function.update_apply, hne, hS])
      all_goals try (have hne := ne_par hb hy; simp [step, h0, hO, e0, Instr.coreOf, RAMStep, State.next,
        apply_ite RAMConfig.mem,
        Function.update_apply, hne])
    | store qq i =>
      simp only [blen, block] at hpos hQat
      rw [rs_addrCode_length b 0 (rr s qq)] at hpos hQat
      have hA := addr_run Q w f St b (rr s qq) hb hO (fun m hm => by
        rw [hQat m (by omega)]; simp [List.getElem?_append_left hm])
      have e0 := hQat _ (Nat.lt_succ_self _)
      simp only [List.getElem?_concat_length] at e0
      have hL2 : (addrCode b (rr s qq)).length ≤ 2 := by unfold addrCode; split_ifs <;> simp
      generalize (addrCode b (rr s qq)).length = L at hA e0 hpos hL2
      refine ⟨L + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply', hA]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals try simp [step, h0, hO, hp, e0, rr_ne_S0 hs, Instr.coreOf, RAMStep, State.next, hpos,
        Function.update_apply, cregs, cptrs, cmem, cimem, ccoins, cqueries, add_assoc,
        apply_ite RAMConfig.pc, apply_ite RAMConfig.regs, apply_ite RAMConfig.ptrs,
        apply_ite RAMConfig.mem, apply_ite (posOf b P base)]
      all_goals try refine ⟨fun i hi _ => ?_, fun j hj hS => ?_, fun y hy => ?_, fun y hy => ?_⟩
      all_goals try (have hne := ne_rr hs hi; simp [step, h0, hO, e0, Instr.coreOf, RAMStep, State.next,
        apply_ite RAMConfig.regs,
        Function.update_apply, hne])
      all_goals try (have hne := ne_rr hs hj; simp [step, h0, hO, e0, Instr.coreOf, RAMStep, State.next,
        apply_ite RAMConfig.ptrs,
        Function.update_apply, hne, hS])
      all_goals try (have hne := ne_par hb hy; simp [step, h0, hO, e0, Instr.coreOf, RAMStep, State.next,
        apply_ite RAMConfig.mem,
        Function.update_apply, hne])
    | accept => exact absurd rfl ha
    | reject => exact absurd rfl hr
    | _ =>
      have e0 := hQat 0 (by simp [blen]); simp [block] at e0
      simp [blen] at hpos
      refine ⟨1, by norm_num, ?_⟩
      simp only [Function.iterate_one]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals try simp [step, h0, hO, hp, e0, rr_ne_S0 hs, Instr.coreOf, RAMStep, State.next, hpos,
        Function.update_apply, cregs, cptrs, cmem, cimem, ccoins, cqueries, add_assoc,
        apply_ite RAMConfig.pc, apply_ite RAMConfig.regs, apply_ite RAMConfig.ptrs,
        apply_ite RAMConfig.mem, apply_ite (posOf b P base)]
      all_goals try refine ⟨fun i hi _ => ?_, fun j hj hS => ?_, fun y hy => ?_, fun y hy => ?_⟩
      all_goals try (have hne := ne_rr hs hi; simp [step, h0, hO, e0, Instr.coreOf, RAMStep, State.next,
        apply_ite RAMConfig.regs,
        Function.update_apply, hne])
      all_goals try (have hne := ne_rr hs hj; simp [step, h0, hO, e0, Instr.coreOf, RAMStep, State.next,
        apply_ite RAMConfig.ptrs,
        Function.update_apply, hne, hS])
      all_goals try (have hne := ne_par hb hy; simp [step, h0, hO, e0, Instr.coreOf, RAMStep, State.next,
        apply_ite RAMConfig.mem,
        Function.update_apply, hne])
  | halt src => exact absurd rfl (hh src)
  | integerLoad d qq =>
    simp only [blen, block] at hpos hQat
    rw [rs_addrCode_length b 0 (rr s qq)] at hpos hQat
    have hA := addr_run Q w f St b (rr s qq) hb hO (fun m hm => by
      rw [hQat m (by omega)]; simp [List.getElem?_append_left hm])
    have e0 := hQat _ (Nat.lt_succ_self _)
    simp only [List.getElem?_concat_length] at e0
    have hL2 : (addrCode b (rr s qq)).length ≤ 2 := by unfold addrCode; split_ifs <;> simp
    generalize (addrCode b (rr s qq)).length = L at hA e0 hpos hL2
    refine ⟨L + 1, by omega, ?_⟩
    rw [Function.iterate_succ_apply', hA]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try simp [step, h0, hO, hp, e0, rr_ne_S0 hs, Instr.coreOf, RAMStep, State.next, hpos,
      Function.update_apply, cregs, cptrs, cmem, cimem, ccoins, cqueries, add_assoc,
      apply_ite RAMConfig.pc, apply_ite RAMConfig.regs, apply_ite RAMConfig.ptrs,
      apply_ite RAMConfig.mem, apply_ite (posOf b P base)]
    all_goals try refine ⟨fun i hi _ => ?_, fun j hj hS => ?_, fun y hy => ?_, fun y hy => ?_⟩
    all_goals try (have hne := ne_rr hs hi; simp [step, h0, hO, e0, Instr.coreOf, RAMStep, State.next,
      apply_ite RAMConfig.regs,
      Function.update_apply, hne])
    all_goals try (have hne := ne_rr hs hj; simp [step, h0, hO, e0, Instr.coreOf, RAMStep, State.next,
      apply_ite RAMConfig.ptrs,
      Function.update_apply, hne, hS])
    all_goals try (have hne := ne_par hb hy; simp [step, h0, hO, e0, Instr.coreOf, RAMStep, State.next,
      apply_ite RAMConfig.mem,
      Function.update_apply, hne])
  | integerStore qq c =>
    simp only [blen, block] at hpos hQat
    rw [rs_addrCode_length b 0 (rr s qq)] at hpos hQat
    have hA := addr_run Q w f St b (rr s qq) hb hO (fun m hm => by
      rw [hQat m (by omega)]; simp [List.getElem?_append_left hm])
    have e0 := hQat _ (Nat.lt_succ_self _)
    simp only [List.getElem?_concat_length] at e0
    have hL2 : (addrCode b (rr s qq)).length ≤ 2 := by unfold addrCode; split_ifs <;> simp
    generalize (addrCode b (rr s qq)).length = L at hA e0 hpos hL2
    refine ⟨L + 1, by omega, ?_⟩
    rw [Function.iterate_succ_apply', hA]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try simp [step, h0, hO, hp, e0, rr_ne_S0 hs, Instr.coreOf, RAMStep, State.next, hpos,
      Function.update_apply, cregs, cptrs, cmem, cimem, ccoins, cqueries, add_assoc,
      apply_ite RAMConfig.pc, apply_ite RAMConfig.regs, apply_ite RAMConfig.ptrs,
      apply_ite RAMConfig.mem, apply_ite (posOf b P base)]
    all_goals try refine ⟨fun i hi _ => ?_, fun j hj hS => ?_, fun y hy => ?_, fun y hy => ?_⟩
    all_goals try (have hne := ne_rr hs hi; simp [step, h0, hO, e0, Instr.coreOf, RAMStep, State.next,
      apply_ite RAMConfig.regs,
      Function.update_apply, hne])
    all_goals try (have hne := ne_rr hs hj; simp [step, h0, hO, e0, Instr.coreOf, RAMStep, State.next,
      apply_ite RAMConfig.ptrs,
      Function.update_apply, hne, hS])
    all_goals try (have hne := ne_par hb hy; simp [step, h0, hO, e0, Instr.coreOf, RAMStep, State.next,
      apply_ite RAMConfig.mem,
      Function.update_apply, hne])
  | _ =>
    have e0 := hQat 0 (by simp [blen]); simp [block] at e0
    simp [blen] at hpos
    refine ⟨1, by norm_num, ?_⟩
    simp only [Function.iterate_one]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try simp [step, h0, hO, hp, e0, rr_ne_S0 hs, Instr.coreOf, RAMStep, State.next, hpos,
      Function.update_apply, cregs, cptrs, cmem, cimem, ccoins, cqueries, add_assoc,
      apply_ite RAMConfig.pc, apply_ite RAMConfig.regs, apply_ite RAMConfig.ptrs,
      apply_ite RAMConfig.mem, apply_ite (posOf b P base)]
    all_goals try refine ⟨fun i hi _ => ?_, fun j hj hS => ?_, fun y hy => ?_, fun y hy => ?_⟩
    all_goals try (have hne := ne_rr hs hi; simp [step, h0, hO, e0, Instr.coreOf, RAMStep, State.next,
      apply_ite RAMConfig.regs,
      Function.update_apply, hne])
    all_goals try (have hne := ne_rr hs hj; simp [step, h0, hO, e0, Instr.coreOf, RAMStep, State.next,
      apply_ite RAMConfig.ptrs,
      Function.update_apply, hne, hS])
    all_goals try (have hne := ne_par hb hy; simp [step, h0, hO, e0, Instr.coreOf, RAMStep, State.next,
      apply_ite RAMConfig.mem,
      Function.update_apply, hne])


/-- A state that does not halt now and is not stuck. -/
def Good (P : Program) (σ : State) : Prop :=
  σ.output = none ∧ ∃ i, P[σ.cfg.pc]? = some i ∧ i ≠ .core .accept ∧ i ≠ .core .reject ∧
    ∀ src, i ≠ .halt src

theorem run_sim {P Q : Program} {s b base cont c0 q0 : ℕ} (hs : s = 1 ∨ s = 2)
    (hb : b = 0 ∨ b = 1)
    (hQ : ∀ k < rlen b P, Q[base + k]? = (reloc s b P base cont)[k]?)
    {n : ℕ} (w : Fin n → Fin n → ℝ) (f : ℕ → Bool) (σ0 St0 : State)
    (hc0 : Corr P s b base c0 q0 σ0 St0) (t : ℕ)
    (hgood : ∀ u < t, Good P ((step P w (fun j => f (c0 + j)))^[u] σ0)) :
    ∃ t' ≤ 3 * t, Corr P s b base c0 q0 ((step P w (fun j => f (c0 + j)))^[t] σ0)
        ((step Q w f)^[t'] St0) ∧ Frame s b St0 ((step Q w f)^[t'] St0) := by
  induction t with
  | zero => exact ⟨0, le_refl _, hc0, Frame.refl _ _ _⟩
  | succ t ih =>
    obtain ⟨t', ht', hc, hfr⟩ := ih (fun u hu => hgood u (by omega))
    obtain ⟨h0, i, hp, ha, hr, hh⟩ := hgood t (by omega)
    obtain ⟨m, hm, hc', hfr'⟩ := sim_one hs hb hQ w f h0 hp ha hr hh hc
    refine ⟨m + t', by omega, ?_, ?_⟩
    · rw [Function.iterate_succ_apply', Function.iterate_add_apply]; exact hc'
    · rw [Function.iterate_add_apply]; exact hfr.trans hfr'

lemma halt_block (Q : Program) {n : ℕ} (w : Fin n → Fin n → ℝ) (tape : ℕ → Bool) (St : State)
    (r cont : ℕ) (h0 : St.output = none)
    (e0 : Q[St.cfg.pc]? = some (.core (.add OUT r ZR)))
    (e1 : Q[St.cfg.pc + 1]? = some (.core (.pjle S0 S0 cont))) :
    (step Q w tape)^[2] St =
      { St with
        cfg := ⟨cont, Function.update St.cfg.regs OUT (St.cfg.regs r + St.cfg.regs ZR),
          St.cfg.ptrs, St.cfg.mem⟩
        work := St.work + 2 } := by
  simp [step, h0, e0, e1, RAMStep, Instr.coreOf, add_assoc]

theorem reloc_sim (P Q : Program) (s b base cont c0 q0 : ℕ) (hs : s = 1 ∨ s = 2) (hb : b = 0 ∨ b = 1)
    (hQ : ∀ k < rlen b P, Q[base + k]? = (reloc s b P base cont)[k]?)
    {n : ℕ} (w : Fin n → Fin n → ℝ) (f : ℕ → Bool) (σ0 St0 : State) (T : ℕ) (z : ℝ)
    (hσ0 : σ0.output = none)
    (hhalt : ((step P w (fun j => f (c0 + j)))^[T] σ0).output = some z)
    (hcorr : Corr P s b base c0 q0 σ0 St0) (hZR : St0.cfg.regs ZR = 0) :
    ∃ T' ≤ 3 * T,
      ((step Q w f)^[T'] St0).cfg.pc = cont ∧
      ((step Q w f)^[T'] St0).cfg.regs OUT = z ∧
      ((step Q w f)^[T'] St0).output = none ∧
      ((step Q w f)^[T'] St0).coins = c0 + ((step P w (fun j => f (c0 + j)))^[T] σ0).coins ∧
      ((step Q w f)^[T'] St0).queries = q0 + ((step P w (fun j => f (c0 + j)))^[T] σ0).queries ∧
      (∀ i, i % 3 ≠ s → i ≠ OUT → ((step Q w f)^[T'] St0).cfg.regs i = St0.cfg.regs i) ∧
      (∀ j, j % 3 ≠ s → j ≠ S0 → ((step Q w f)^[T'] St0).cfg.ptrs j = St0.cfg.ptrs j) ∧
      (∀ y : ℤ, y % 2 ≠ (b : ℤ) → ((step Q w f)^[T'] St0).cfg.mem y = St0.cfg.mem y) ∧
      (∀ y : ℤ, y % 2 ≠ (b : ℤ) → ((step Q w f)^[T'] St0).imem y = St0.imem y) := by
  classical
  set g : ℕ → Bool := fun j => f (c0 + j) with hg
  set σ : ℕ → State := fun u => (step P w g)^[u] σ0 with hσdef
  have hσs : ∀ u, σ (u + 1) = step P w g (σ u) := fun u => Function.iterate_succ_apply' _ _ _
  have hex : ∃ u, (σ u).output.isSome := ⟨T, by simp [σ, hhalt]⟩
  set u := Nat.find hex with hu
  have huS : (σ u).output.isSome := Nat.find_spec hex
  have hmin : ∀ v < u, (σ v).output = none := fun v hv => by
    have := Nat.find_min hex hv; simpa using this
  have huT : u ≤ T := Nat.find_min' hex (by simp [σ, hhalt])
  have hu0 : u ≠ 0 := by intro h; rw [h] at huS; simp [σ, hσ0] at huS
  clear_value u
  obtain ⟨t, rfl⟩ : ∃ t, u = t + 1 := ⟨u - 1, by omega⟩
  -- no state before `T` is stuck
  have hns : ∀ v ≤ T, ¬ Stuck P (σ v) := by
    intro v hv hst
    have h := (stuck_iterate w g P _ hst (T - v)).1
    simp only [σ] at h
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hv, hhalt] at h
    cases h
  have hinstr : ∀ v ≤ T, (σ v).output = none → ∃ i, P[(σ v).cfg.pc]? = some i ∧
      i ≠ .core .accept ∧ i ≠ .core .reject := by
    intro v hv h0
    match hq : P[(σ v).cfg.pc]? with
    | none => exact absurd ⟨h0, Or.inl hq⟩ (hns v hv)
    | some i =>
      refine ⟨i, rfl, ?_, ?_⟩
      · rintro rfl; exact hns v hv ⟨h0, Or.inr (Or.inl hq)⟩
      · rintro rfl; exact hns v hv ⟨h0, Or.inr (Or.inr hq)⟩
  have hgood : ∀ v < t, Good P (σ v) := by
    intro v hv
    have h0 := hmin v (by omega)
    obtain ⟨i, hp, ha, hr⟩ := hinstr v (by omega) h0
    refine ⟨h0, i, hp, ha, hr, ?_⟩
    rintro src rfl
    have h1 := hmin (v + 1) (by omega)
    rw [hσs, step_halt w g P _ src h0 hp] at h1
    cases h1
  -- the last step is a `halt`
  have ht0 := hmin t (by omega)
  obtain ⟨i, hp, -, -⟩ := hinstr t (by omega) ht0
  obtain ⟨src, rfl⟩ : ∃ src, i = .halt src := by
    by_contra hne
    have := step_output_none w g P _ i ht0 hp (fun src h => hne ⟨src, h⟩)
    rw [← hσs] at this
    simp [this] at huS
  have hσu := step_halt w g P _ src ht0 hp
  rw [← hσs] at hσu
  have hσT : (step P w g)^[T] σ0 = σ (t + 1) := by
    have : (σ (t + 1)).output = some ((σ t).cfg.regs src) := by rw [hσu]
    have h2 := rs_iterate_halted w g P _ this (T - (t + 1))
    simp only [σ] at h2 ⊢
    rwa [← Function.iterate_add_apply, Nat.sub_add_cancel huT] at h2
  rw [hσT] at hhalt ⊢
  rw [hσu] at hhalt ⊢
  simp only [Option.some.injEq] at hhalt
  -- simulate up to time `t`
  obtain ⟨t', ht', hc, hfr⟩ := run_sim hs hb hQ w f σ0 St0 hcorr t hgood
  obtain ⟨hk, hPk⟩ := List.getElem?_eq_some_iff.mp hp
  have e0 := Qat hQ hc hk 0 (by rw [hPk]; simp [blen])
  have e1 := Qat hQ hc hk 1 (by rw [hPk]; simp [blen])
  rw [hPk] at e0 e1
  simp [block] at e0 e1
  have hfin := halt_block Q w f _ (rr s src) cont hc.outSt e0 e1
  rw [← Function.iterate_add_apply] at hfin
  have hZR' : ((step Q w f)^[t'] St0).cfg.regs ZR = 0 := by
    rw [hfr.regs ZR (by unfold ZR; omega) (by unfold ZR OUT; omega), hZR]
  refine ⟨2 + t', by omega, ?_⟩
  rw [hfin]
  refine ⟨rfl, ?_, hc.outSt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hc.regs, hZR']; exact hhalt
  · simp [hc.coins]; rfl
  · simp [hc.queries]; rfl
  · intro i hi hO
    simp [hO, hfr.regs i hi hO]
  · intro j hj hS; simp [hfr.ptrs j hj hS]
  · intro y hy; simp [hfr.mem y hy]
  · intro y hy; simp [hfr.imem y hy]

end MTSPComp



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



namespace MTSPCount

open scoped Classical
open SublinearSteiner

/-- Phase-2 bound (xor-window averaging). -/
theorem bad2_bound {α : Type*} (B B1 B2 : ℕ) (hB : B1 + B2 ≤ B)
    (g : (ℕ → Bool) → ℕ × α)
    (hk : ∀ f, (g f).1 ≤ B1)
    (hdet : ∀ f f', (∀ j < (g f).1, f j = f' j) → g f' = g f)
    (G1 : α → Prop) (G2 : α → (Fin B2 → Bool) → Prop)
    (h2 : ∀ a, G1 a → 6 * (Finset.univ.filter (fun σ : Fin B2 → Bool => ¬ G2 a σ)).card
      ≤ 2 ^ B2) :
    6 * (Finset.univ.filter (fun t : Fin B → Bool =>
        G1 (g (extendTape t)).2 ∧
        ¬ G2 (g (extendTape t)).2 (fun i : Fin B2 => extendTape t ((g (extendTape t)).1 + i)))).card
      ≤ 2 ^ B := by
  set k : (Fin B → Bool) → ℕ := fun t => (g (extendTape t)).1 with hkdef
  set a : (Fin B → Bool) → α := fun t => (g (extendTape t)).2 with hadef
  set w : (Fin B → Bool) → Fin B2 → Bool := fun t i => extendTape t (k t + i) with hwdef
  let φ : (Fin B2 → Bool) → (Fin B → Bool) → (Fin B → Bool) := fun σ t j =>
    if h : k t ≤ j.val ∧ j.val < k t + B2 then
      xor (t j) (σ ⟨j.val - k t, by omega⟩) else t j
  have hφg : ∀ σ t, g (extendTape (φ σ t)) = g (extendTape t) := by
    intro σ t
    apply hdet
    intro j hj
    have hjB : j < B := by
      have := hk (extendTape t); omega
    simp only [extendTape, hjB, dite_true, φ]
    rw [dif_neg]
    intro h
    exact absurd h.1 (by simp only [k]; omega)
  have hφk : ∀ σ t, k (φ σ t) = k t := fun σ t => by simp only [k, hφg]
  have hφa : ∀ σ t, a (φ σ t) = a t := fun σ t => by simp only [a, hφg]
  have hφw : ∀ σ t i, w (φ σ t) i = xor (w t i) (σ i) := by
    intro σ t i
    have hkt := hk (extendTape t)
    have hlt : k t + i.val < B := by simp only [k]; omega
    simp only [w, hφk]
    simp only [extendTape, hlt, dite_true, φ]
    rw [dif_pos ⟨by simp, by simp⟩]
    congr 2
    ext; simp
  have hφφ : ∀ σ t, φ σ (φ σ t) = t := by
    intro σ t
    funext j
    have e1 : φ σ (φ σ t) j = if h : k t ≤ j.val ∧ j.val < k t + B2 then
        xor (φ σ t j) (σ ⟨j.val - k t, by omega⟩) else φ σ t j := by
      show (if h : k (φ σ t) ≤ j.val ∧ j.val < k (φ σ t) + B2 then
        xor (φ σ t j) (σ ⟨j.val - k (φ σ t), by omega⟩) else φ σ t j) = _
      simp only [hφk]
    rw [e1]
    by_cases h : k t ≤ j.val ∧ j.val < k t + B2
    · rw [dif_pos h]
      show xor (if h : k t ≤ j.val ∧ j.val < k t + B2 then
        xor (t j) (σ ⟨j.val - k t, by omega⟩) else t j) _ = _
      rw [dif_pos h]; simp
    · rw [dif_neg h]
      show (if h : k t ≤ j.val ∧ j.val < k t + B2 then
        xor (t j) (σ ⟨j.val - k t, by omega⟩) else t j) = _
      rw [dif_neg h]
  set Bad2 := Finset.univ.filter (fun t : Fin B → Bool => G1 (a t) ∧ ¬ G2 (a t) (w t))
    with hBad2
  let S : (Fin B2 → Bool) → Finset (Fin B → Bool) := fun σ =>
    Finset.univ.filter (fun t => G1 (a t) ∧ ¬ G2 (a t) (fun i => xor (w t i) (σ i)))
  have hS : ∀ σ, (S σ).card = Bad2.card := by
    intro σ
    apply Finset.card_nbij' (φ σ) (φ σ)
    · intro t ht
      simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
      simp only [hBad2, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      rw [hφa]
      refine ⟨ht.1, ?_⟩
      have : w (φ σ t) = fun i => xor (w t i) (σ i) := funext (hφw σ t)
      rw [this]; exact ht.2
    · intro t ht
      simp only [hBad2, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht
      simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      rw [hφa]
      refine ⟨ht.1, ?_⟩
      have : (fun i => xor (w (φ σ t) i) (σ i)) = w t := by
        funext i; rw [hφw]; simp
      rw [this]; exact ht.2
    · intro t _; exact hφφ σ t
    · intro t _; exact hφφ σ t
  -- inner bound
  have hinner : ∀ t, 6 * (∑ σ : Fin B2 → Bool,
      if (G1 (a t) ∧ ¬ G2 (a t) (fun i => xor (w t i) (σ i))) then 1 else 0) ≤ 2 ^ B2 := by
    intro t
    by_cases hg : G1 (a t)
    · simp only [hg, true_and]
      rw [← Finset.card_filter]
      have : (Finset.univ.filter (fun σ : Fin B2 → Bool =>
          ¬ G2 (a t) (fun i => xor (w t i) (σ i)))).card =
          (Finset.univ.filter (fun σ : Fin B2 → Bool => ¬ G2 (a t) σ)).card := by
        apply Finset.card_nbij' (fun σ i => xor (w t i) (σ i)) (fun σ i => xor (w t i) (σ i))
        · intro σ hσ
          simpa using hσ
        · intro σ hσ
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
          have : (fun i => xor (w t i) (xor (w t i) (σ i))) = σ := by funext i; simp
          rw [this]; exact hσ
        · intro σ _; funext i; simp
        · intro σ _; funext i; simp
      rw [this]; exact h2 _ hg
    · simp [hg]
  have hsum : ∑ σ : Fin B2 → Bool, (S σ).card = 2 ^ B2 * Bad2.card := by
    simp only [hS, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, smul_eq_mul]
  have hsum2 : ∑ σ : Fin B2 → Bool, (S σ).card = ∑ t : Fin B → Bool, ∑ σ : Fin B2 → Bool,
      (if (G1 (a t) ∧ ¬ G2 (a t) (fun i => xor (w t i) (σ i))) then 1 else 0) := by
    simp only [S, Finset.card_filter]
    exact Finset.sum_comm
  have hfin : 6 * (2 ^ B2 * Bad2.card) ≤ 2 ^ B * 2 ^ B2 := by
    rw [← hsum, hsum2, Finset.mul_sum]
    calc ∑ t : Fin B → Bool, 6 * (∑ σ : Fin B2 → Bool,
          (if (G1 (a t) ∧ ¬ G2 (a t) (fun i => xor (w t i) (σ i))) then 1 else 0))
        ≤ ∑ t : Fin B → Bool, 2 ^ B2 := Finset.sum_le_sum (fun t _ => hinner t)
      _ = 2 ^ B * 2 ^ B2 := by
        simp [Finset.sum_const, Finset.card_univ]
  have hpos : 0 < 2 ^ B2 := by positivity
  have : 6 * Bad2.card * 2 ^ B2 ≤ 2 ^ B * 2 ^ B2 := by
    calc 6 * Bad2.card * 2 ^ B2 = 6 * (2 ^ B2 * Bad2.card) := by ring
      _ ≤ _ := hfin
  exact Nat.le_of_mul_le_mul_right this hpos

/-- Phase-1 bound (restriction to the first `B1` bits). -/
theorem bad1_bound {α : Type*} (B1 D : ℕ)
    (g : (ℕ → Bool) → ℕ × α)
    (hk : ∀ f, (g f).1 ≤ B1)
    (hdet : ∀ f f', (∀ j < (g f).1, f j = f' j) → g f' = g f)
    (G1 : α → Prop)
    (h1 : 6 * (Finset.univ.filter (fun τ : Fin B1 → Bool => ¬ G1 (g (extendTape τ)).2)).card
      ≤ 2 ^ B1) :
    6 * (Finset.univ.filter (fun t : Fin (B1 + D) → Bool =>
        ¬ G1 (g (extendTape t)).2)).card ≤ 2 ^ (B1 + D) := by
  let e : (Fin (B1 + D) → Bool) ≃ (Fin B1 → Bool) × (Fin D → Bool) :=
    (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _)
  have he : ∀ t (i : Fin B1), (e t).1 i = t (Fin.castAdd D i) := by
    intro t i; simp [e, Equiv.arrowCongr]
  have hg : ∀ t, g (extendTape t) = g (extendTape (e t).1) := by
    intro t
    apply hdet
    intro j hj
    have hj1 : j < B1 := lt_of_lt_of_le hj (hk _)
    have hj2 : j < B1 + D := by omega
    simp only [extendTape, hj1, hj2, dite_true, he]
    rfl
  have hcard : (Finset.univ.filter (fun t : Fin (B1 + D) → Bool =>
        ¬ G1 (g (extendTape t)).2)).card =
      ((Finset.univ.filter (fun τ : Fin B1 → Bool => ¬ G1 (g (extendTape τ)).2)) ×ˢ
        (Finset.univ : Finset (Fin D → Bool))).card := by
    apply Finset.card_nbij' e e.symm
    · intro t ht
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht
      simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and,
        Finset.coe_univ, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_univ, and_true]
      rw [← hg]; exact ht
    · intro p hp
      simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and,
        Finset.coe_univ, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_univ, and_true] at hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      rw [hg]; simpa using hp
    · intro t _; simp
    · intro p _; simp
  rw [hcard, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, pow_add, ← mul_assoc]
  exact Nat.mul_le_mul_right _ h1

theorem compose_count {α : Type*} (B B1 B2 : ℕ) (hB : B1 + B2 ≤ B)
    (g : (ℕ → Bool) → ℕ × α)
    (hk : ∀ f, (g f).1 ≤ B1)
    (hdet : ∀ f f', (∀ j < (g f).1, f j = f' j) → g f' = g f)
    (G1 : α → Prop) (G2 : α → (Fin B2 → Bool) → Prop)
    (h1 : (5 / 6 : ℝ) * 2 ^ B1 ≤
      ((Finset.univ.filter (fun τ : Fin B1 → Bool => G1 (g (extendTape τ)).2)).card : ℝ))
    (h2 : ∀ a, G1 a → (5 / 6 : ℝ) * 2 ^ B2 ≤
      ((Finset.univ.filter (fun σ : Fin B2 → Bool => G2 a σ)).card : ℝ)) :
    (2 / 3 : ℝ) * 2 ^ B ≤
      ((Finset.univ.filter (fun t : Fin B → Bool =>
        G1 (g (extendTape t)).2 ∧
        G2 (g (extendTape t)).2 (fun i : Fin B2 => extendTape t ((g (extendTape t)).1 + i)))).card : ℝ) := by
  -- complement bounds in ℕ
  have compl : ∀ (n : ℕ) (P : (Fin n → Bool) → Prop),
      (Finset.univ.filter (fun x => P x)).card + (Finset.univ.filter (fun x => ¬ P x)).card
        = 2 ^ n := by
    intro n P
    rw [Finset.card_filter_add_card_filter_not]
    simp
  have h1' : 6 * (Finset.univ.filter (fun τ : Fin B1 → Bool => ¬ G1 (g (extendTape τ)).2)).card
      ≤ 2 ^ B1 := by
    have hc := compl B1 (fun τ => G1 (g (extendTape τ)).2)
    have hc' : ((Finset.univ.filter (fun τ : Fin B1 → Bool => G1 (g (extendTape τ)).2)).card : ℝ)
        + ((Finset.univ.filter (fun τ : Fin B1 → Bool => ¬ G1 (g (extendTape τ)).2)).card : ℝ)
        = 2 ^ B1 := by exact_mod_cast hc
    have : (6 * (Finset.univ.filter (fun τ : Fin B1 → Bool =>
        ¬ G1 (g (extendTape τ)).2)).card : ℝ) ≤ 2 ^ B1 := by linarith
    exact_mod_cast this
  have h2' : ∀ a, G1 a → 6 * (Finset.univ.filter (fun σ : Fin B2 → Bool => ¬ G2 a σ)).card
      ≤ 2 ^ B2 := by
    intro a ha
    have hc := compl B2 (fun σ => G2 a σ)
    have hc' : ((Finset.univ.filter (fun σ : Fin B2 → Bool => G2 a σ)).card : ℝ)
        + ((Finset.univ.filter (fun σ : Fin B2 → Bool => ¬ G2 a σ)).card : ℝ)
        = 2 ^ B2 := by exact_mod_cast hc
    have h := h2 a ha
    have : (6 * (Finset.univ.filter (fun σ : Fin B2 → Bool => ¬ G2 a σ)).card : ℝ)
        ≤ 2 ^ B2 := by linarith
    exact_mod_cast this
  have hb2 := bad2_bound B B1 B2 hB g hk hdet G1 G2 h2'
  obtain ⟨D, rfl⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right B1 B2) hB)
  have hb1 := bad1_bound B1 D g hk hdet G1 h1'
  set Good := Finset.univ.filter (fun t : Fin (B1 + D) → Bool =>
        G1 (g (extendTape t)).2 ∧
        G2 (g (extendTape t)).2 (fun i : Fin B2 => extendTape t ((g (extendTape t)).1 + i)))
  set Bad1 := Finset.univ.filter (fun t : Fin (B1 + D) → Bool => ¬ G1 (g (extendTape t)).2)
  set Bad2 := Finset.univ.filter (fun t : Fin (B1 + D) → Bool =>
        G1 (g (extendTape t)).2 ∧
        ¬ G2 (g (extendTape t)).2 (fun i : Fin B2 => extendTape t ((g (extendTape t)).1 + i)))
  have hcov : (Finset.univ : Finset (Fin (B1 + D) → Bool)) ⊆ Good ∪ Bad1 ∪ Bad2 := by
    intro t _
    simp only [Good, Bad1, Bad2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hle : 2 ^ (B1 + D) ≤ Good.card + Bad1.card + Bad2.card := by
    have := Finset.card_le_card hcov
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
    exact this.trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hnat : 2 * 2 ^ (B1 + D) ≤ 3 * Good.card := by omega
  have : ((2 * 2 ^ (B1 + D) : ℕ) : ℝ) ≤ ((3 * Good.card : ℕ) : ℝ) := by exact_mod_cast hnat
  push_cast at this
  linarith

end MTSPCount



open scoped Classical

namespace MTSPThm1
open SublinearSteiner MTSPComp MetricTSPSublinear

/-- The decision value. -/
noncomputable def dec (e : ℚ) (z L : ℝ) : ℝ :=
  if ((1 + e : ℚ) : ℝ) * z / 2 ≤ L then 2 * z else ((2 - e : ℚ) : ℝ) * z

/-- Phase 1 on an infinite tape. -/
noncomputable def r1 (P1 : Program) {n : ℕ} (d : Fin n → Fin n → ℝ) (B1 : ℕ) (f : ℕ → Bool) : State :=
  (step P1 d f)^[B1] (initState (Finset.univ : Finset (Fin n)))

/-- Phase 2 on an infinite tape. -/
noncomputable def r2 (P2 : Program) {n : ℕ} (d : Fin n → Fin n → ℝ) (B2 : ℕ) (z : ℝ) (f : ℕ → Bool) : State :=
  (step P2 d f)^[B2] (initWithEstimate n z)

lemma r1_eq (P1 : Program) {n : ℕ} (d : Fin n → Fin n → ℝ) (B1 : ℕ) (f : ℕ → Bool) :
    r1 P1 d B1 f = run P1 Finset.univ d (fun i : Fin B1 => f i) B1 := by
  unfold r1 run
  apply iterate_congr_tape
  intro j hj
  have := coins_le P1 d f (initState (Finset.univ : Finset (Fin n))) B1
  have h0 : (initState (Finset.univ : Finset (Fin n))).coins = 0 := rfl
  have hjB : j < B1 := by omega
  simp [extendTape, hjB]

lemma r2_eq (P2 : Program) {n : ℕ} (d : Fin n → Fin n → ℝ) (B2 : ℕ) (z : ℝ) (f : ℕ → Bool) :
    r2 P2 d B2 z f = runWithEstimate P2 d z (fun i : Fin B2 => f i) B2 := by
  unfold r2 runWithEstimate
  apply iterate_congr_tape
  intro j hj
  have := coins_le P2 d f (initWithEstimate n z) B2
  have h0 : (initWithEstimate n z).coins = 0 := rfl
  have hjB : j < B2 := by omega
  simp [extendTape, hjB]

lemma iter_add (Q : Program) {n : ℕ} (d : Fin n → Fin n → ℝ) (f : ℕ → Bool) (a b : ℕ) (s : State) :
    (step Q d f)^[a] ((step Q d f)^[b] s) = (step Q d f)^[a + b] s :=
  (Function.iterate_add_apply _ a b s).symm

/-- One run of the composite program. -/
theorem composite_run (e : ℚ) (P1 P2 : Program) {n : ℕ} (d : Fin n → Fin n → ℝ) (B1 B2 : ℕ)
    (f : ℕ → Bool) (z L : ℝ)
    (hz : (r1 P1 d B1 f).output = some z)
    (hL : (r2 P2 d B2 z (fun j => f ((r1 P1 d B1 f).coins + j))).output = some L) :
    ∃ Tq ≤ 8 * (n + 1) + 5 + 3 * B1 + 3 + 3 * B2 + 7,
      ((step (composite e P1 P2) d f)^[Tq] (initState (Finset.univ : Finset (Fin n)))).output =
        some (dec e z L) ∧
      ((step (composite e P1 P2) d f)^[Tq] (initState (Finset.univ : Finset (Fin n)))).queries =
        (r1 P1 d B1 f).queries + (r2 P2 d B2 z (fun j => f ((r1 P1 d B1 f).coins + j))).queries := by
  set Q := composite e P1 P2 with hQdef
  set I0 := initState (Finset.univ : Finset (Fin n)) with hI0
  -- copy loop
  obtain ⟨hc_pc, hc_out, hc_coins, hc_q, hc_regs, hc_ptrs, hc_mem, hc_im0, hc_im1⟩ :=
    copy_run Q (composite_copy e P1 P2) d f
  set Sc := (step Q d f)^[8 * (n + 1) + 5] I0 with hSc
  -- phase 1
  have hcorr1 : Corr P1 1 1 copyCode.length 0 0 I0 Sc := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hc_out⟩
    · rw [hc_pc, hI0]; simp [posOf, initState]; rfl
    · intro i; rw [hc_regs]; rfl
    · intro j; rw [hc_ptrs _ (by simp only [rr]; omega)]; rfl
    · intro x; rw [hc_mem]; rfl
    · intro x; exact hc_im1 x
    · rw [hc_coins]; rfl
    · rw [hc_q]; rfl
  have hhalt1 : ((step P1 d (fun j => f (0 + j)))^[B1] I0).output = some z := by
    simpa [r1] using hz
  obtain ⟨T1, hT1, h1pc, h1out, h1none, h1coins, h1q, h1regs, h1ptrs, h1mem, h1imem⟩ :=
    reloc_sim P1 Q 1 1 copyCode.length (midPos P1) 0 0 (Or.inl rfl) (Or.inr rfl)
      (composite_r1 e P1 P2) d f I0 Sc B1 z rfl hhalt1 hcorr1 (hc_regs _)
  simp only [zero_add] at h1coins h1q
  set S1 := (step Q d f)^[T1] Sc with hS1
  -- middle
  have hZR1 : S1.cfg.regs ZR = 0 := by
    rw [h1regs ZR (by decide) (by decide)]; exact hc_regs _
  obtain ⟨hm_pc, hm_out, hm_coins, hm_q, hm_mem0, hm_mem, hm_r6, hm_regs, hm_ptrs, hm_imem⟩ :=
    mid_run Q (midPos P1) (composite_mid e P1 P2) d f S1 h1pc h1none hZR1
  set Sm := (step Q d f)^[3] S1 with hSm
  set k := (r1 P1 d B1 f).coins with hk
  have hk' : ((step P1 d (fun j => f (0 + j)))^[B1] I0).coins = k := by simp only [zero_add]; rfl
  have hq' : ((step P1 d (fun j => f (0 + j)))^[B1] I0).queries = (r1 P1 d B1 f).queries := by
    simp only [zero_add]; rfl
  have hcorr2 : Corr P2 2 0 (base2 P1) k (r1 P1 d B1 f).queries (initWithEstimate n z) Sm := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hm_out⟩
    · rw [hm_pc]; simp [posOf, base2]; rfl
    · intro i
      rw [hm_regs _ (by simp only [rr]; omega), h1regs _ (by simp only [rr]; omega) (by simp only [rr, OUT]; omega),
        hc_regs]; rfl
    · intro j
      rw [hm_ptrs _ (by simp only [rr]; omega), h1ptrs _ (by simp only [rr]; omega) (by simp only [rr, S0]; omega),
        hc_ptrs _ (by simp only [rr]; omega)]; rfl
    · intro x
      by_cases hx : x = 0
      · subst hx; simp only [mul_zero, Nat.cast_zero, add_zero]
        rw [hm_mem0, h1out]
        simp [initWithEstimate]
      · have h2x : 2 * x + ((0 : ℕ) : ℤ) ≠ 0 := by omega
        rw [hm_mem _ h2x, h1mem _ (by push_cast; omega), hc_mem]
        simp [initWithEstimate, Function.update, hx, initState]
    · intro x
      rw [hm_imem, h1imem _ (by push_cast; omega)]
      have := hc_im0 x
      simp only [Nat.cast_zero, add_zero]
      rw [this]; rfl
    · rw [hm_coins, h1coins]; simp only [zero_add] at hk' ⊢; rw [hk']; rfl
    · rw [hm_q, h1q]; simp only [zero_add] at hq' ⊢; rw [hq']; rfl
  have hZR2 : Sm.cfg.regs ZR = 0 := by rw [hm_regs ZR (by decide)]; exact hZR1
  have hhalt2 : ((step P2 d (fun j => f (k + j)))^[B2] (initWithEstimate n z)).output = some L := by
    simpa [r2] using hL
  obtain ⟨T2, hT2, h2pc, h2out, h2none, h2coins, h2q, h2regs, h2ptrs, h2mem, h2imem⟩ :=
    reloc_sim P2 Q 2 0 (base2 P1) (tailPos P1 P2) k (r1 P1 d B1 f).queries (Or.inr rfl) (Or.inl rfl)
      (composite_r2 e P1 P2) d f (initWithEstimate n z) Sm B2 L rfl hhalt2 hcorr2 hZR2
  set S2 := (step Q d f)^[T2] Sm with hS2
  have h6 : S2.cfg.regs 6 = z := by
    rw [h2regs 6 (by decide) (by decide), hm_r6, h1out]
  obtain ⟨ht_out, ht_q⟩ := tail_run Q e (tailPos P1 P2) (composite_tail e P1 P2) d f S2 h2pc h2none
  refine ⟨7 + (T2 + (3 + (T1 + (8 * (n + 1) + 5)))), by omega, ?_, ?_⟩
  · rw [← iter_add, ← iter_add, ← iter_add, ← iter_add]
    rw [ht_out, h6, h2out]; rfl
  · rw [← iter_add, ← iter_add, ← iter_add, ← iter_add]
    rw [ht_q, h2q]
    simp [r2]

end MTSPThm1



namespace MTSPComp
open SublinearSteiner SmaleNinth

lemma block_adm (s b : ℕ) (pos : ℕ → ℕ) (cont : ℕ) (i : Instr)
    (hi : (∀ d c, i = .core (.const d c) → ∃ q : ℚ, c = (q : ℝ)) ∧
      i ≠ .core .accept ∧ i ≠ .core .reject) :
    ∀ j ∈ block s b pos cont i, (∀ d c, j = .core (.const d c) → ∃ q : ℚ, c = (q : ℝ)) ∧
      j ≠ .core .accept ∧ j ≠ .core .reject := by
  obtain ⟨hc, ha, hr⟩ := hi
  intro j hj
  cases i with
  | core i =>
    cases i with
    | const d0 c0 =>
      simp only [block, List.mem_singleton] at hj; subst hj
      refine ⟨fun d c h => ?_, by simp, by simp⟩
      simp only [Instr.core.injEq, RAMInstr.const.injEq] at h
      obtain ⟨q, hq⟩ := hc d0 c0 rfl
      exact ⟨q, h.2 ▸ hq⟩
    | accept => exact absurd rfl ha
    | reject => exact absurd rfl hr
    | _ =>
      simp only [block, addrCode] at hj
      (try split_ifs at hj) <;> simp at hj <;> aesop
  | _ =>
    simp only [block, addrCode] at hj
    (try split_ifs at hj) <;> simp at hj <;> aesop

lemma reloc_adm (s b : ℕ) (P : Program) (base cont : ℕ) (hP : Admissible P) :
    Admissible (reloc s b P base cont) := by
  intro j hj
  simp only [reloc, List.mem_flatten, List.mem_map] at hj
  obtain ⟨_, ⟨i, hi, rfl⟩, hj⟩ := hj
  exact block_adm s b _ cont i (hP i hi) j hj

lemma append_adm {P Q : Program} (hP : Admissible P) (hQ : Admissible Q) : Admissible (P ++ Q) := by
  intro i hi
  rcases List.mem_append.mp hi with h | h
  · exact hP i h
  · exact hQ i h

lemma composite_adm (e : ℚ) (P1 P2 : Program) (h1 : Admissible P1) (h2 : Admissible P2) :
    Admissible (composite e P1 P2) := by
  unfold composite
  refine append_adm (append_adm (append_adm (append_adm ?_ (reloc_adm _ _ _ _ _ h1)) ?_)
    (reloc_adm _ _ _ _ _ h2)) ?_
  · intro i hi
    simp only [copyCode, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro i hi
    simp only [midCode, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> simp
  · intro i hi
    simp only [tailCode, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · exact ⟨(1 + e) / 2, by push_cast; ring⟩
    · exact ⟨2 - e, by push_cast; ring⟩
    · exact ⟨2, by norm_num⟩

end MTSPComp



open scoped Classical

namespace MTSPThm1
open SublinearSteiner MTSPComp MetricTSPSublinear

lemma ceil_le_abs (a : ℝ) : (⌈a⌉₊ : ℝ) ≤ |a| + 1 := by
  rcases le_or_gt a 0 with h | h
  · rw [Nat.ceil_eq_zero.mpr h]; simp; positivity
  · have := Nat.ceil_lt_add_one h.le
    rw [abs_of_pos h]; linarith

lemma rpow_mono_base (n : ℕ) {a b : ℝ} (hab : a ≤ b) : ((n : ℝ) + 1) ^ a ≤ ((n : ℝ) + 1) ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hab

theorem theorem_1_sol :
    ∃ (ε δ γ : ℝ) (P : SublinearSteiner.Program) (C : ℝ), 0 < ε ∧ 0 < δ ∧ 0 < γ ∧
      SublinearSteiner.Admissible P ∧
      ∀ (n : ℕ) (d : Fin n → Fin n → ℝ), DoublingMST.IsMetric d →
        (∀ tape : Fin ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ → Bool,
            (SublinearSteiner.run P Finset.univ d tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).output.isSome ∧
            ((SublinearSteiner.run P Finset.univ d tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).queries : ℝ) ≤
              C * ((n : ℝ) + 1) ^ (2 - ε)) ∧
        (2 / 3 : ℝ) * 2 ^ ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ ≤
          ((Finset.univ.filter (fun tape : Fin ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ → Bool => ∃ z : ℝ,
              (SublinearSteiner.run P Finset.univ d tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).output = some z ∧
              MetricTSP.tspOpt d ≤ z ∧ z ≤ (2 - δ) * MetricTSP.tspOpt d)).card : ℝ) := by
  obtain ⟨ε, γB, ηB, P2, CB, hε0, hε1, hγB, hηB, hadm2, hB⟩ := lemma_9_1_timed
  obtain ⟨e, he1, he2⟩ := exists_rat_btwn (show ε / 2 < ε by linarith)
  have he0 : (0 : ℝ) < e := by linarith
  obtain ⟨εA, γA, P1, CA, hεA, hγA, hadm1, hA⟩ := mst_estimator_program ((e : ℝ) / 4) (by positivity)
  set γ := min (min γA γB) 1 with hγ
  set εq := min εA ηB with hεq
  set C := 3 * |CA| + 3 * |CB| + 40 with hC
  have hγ0 : 0 < γ := lt_min (lt_min hγA hγB) one_pos
  refine ⟨εq, (e : ℝ) / 2, γ, composite e P1 P2, C, lt_min hεA hηB, by positivity, hγ0,
    composite_adm e P1 P2 hadm1 hadm2, ?_⟩
  intro n d hd
  obtain ⟨hA1, hA2⟩ := hA n d hd
  obtain ⟨hB1, hB2⟩ := hB n d hd
  set B1 := ⌈CA * ((n : ℝ) + 1) ^ (2 - γA)⌉₊ with hB1def
  set B2 := ⌈CB * ((n : ℝ) + 1) ^ (2 - γB)⌉₊ with hB2def
  set B := ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ with hBdef
  set Q := composite e P1 P2 with hQ
  -- arithmetic on the budgets
  set x := ((n : ℝ) + 1) ^ (2 - γ) with hx
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hγ1 : γ ≤ 1 := min_le_right _ _
  have hx1 : (n : ℝ) + 1 ≤ x := by
    have := rpow_mono_base n (show (1 : ℝ) ≤ 2 - γ by linarith)
    simpa using this
  have hxpos : 1 ≤ x := hn1.trans hx1
  have hpA : ((n : ℝ) + 1) ^ (2 - γA) ≤ x :=
    rpow_mono_base n (by linarith [min_le_left (min γA γB) 1, min_le_left γA γB])
  have hpB : ((n : ℝ) + 1) ^ (2 - γB) ≤ x :=
    rpow_mono_base n (by linarith [min_le_left (min γA γB) 1, min_le_right γA γB])
  have hB1le : (B1 : ℝ) ≤ |CA| * x + 1 := by
    refine (ceil_le_abs _).trans ?_
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (2 - γA))]
    nlinarith [abs_nonneg CA]
  have hB2le : (B2 : ℝ) ≤ |CB| * x + 1 := by
    refine (ceil_le_abs _).trans ?_
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (2 - γB))]
    nlinarith [abs_nonneg CB]
  have hBge : C * x ≤ (B : ℝ) := Nat.le_ceil _
  have hTle : 8 * (n + 1) + 5 + 3 * B1 + 3 + 3 * B2 + 7 ≤ B := by
    have : ((8 * (n + 1) + 5 + 3 * B1 + 3 + 3 * B2 + 7 : ℕ) : ℝ) ≤ B := by
      push_cast
      nlinarith [abs_nonneg CA, abs_nonneg CB]
    exact_mod_cast this
  have hB12 : B1 + B2 ≤ B := by omega
  -- queries
  have hqA : ∀ τ : Fin B1 → Bool, ((run P1 Finset.univ d τ B1).queries : ℝ) ≤ |CA| * ((n : ℝ) + 1) ^ (2 - εq) := by
    intro τ
    refine (hA1 τ).2.trans ?_
    have h1 : ((n : ℝ) + 1) ^ (2 - εA) ≤ ((n : ℝ) + 1) ^ (2 - εq) :=
      rpow_mono_base n (by linarith [min_le_left εA ηB])
    have h2 : CA ≤ |CA| := le_abs_self CA
    have h3 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (2 - εA) := by positivity
    nlinarith [abs_nonneg CA]
  have hqB : ∀ (M : ℝ) (σ : Fin B2 → Bool),
      ((runWithEstimate P2 d M σ B2).queries : ℝ) ≤ |CB| * ((n : ℝ) + 1) ^ (2 - εq) := by
    intro M σ
    refine (hB1 M σ).2.trans ?_
    have h1 : ((n : ℝ) + 1) ^ (2 - ηB) ≤ ((n : ℝ) + 1) ^ (2 - εq) :=
      rpow_mono_base n (by linarith [min_le_right εA ηB])
    have h2 : CB ≤ |CB| := le_abs_self CB
    have h3 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (2 - ηB) := by positivity
    nlinarith [abs_nonneg CB]
  -- phase outputs exist on every tape
  have hz : ∀ f : ℕ → Bool, ∃ z, (r1 P1 d B1 f).output = some z := by
    intro f
    rw [r1_eq]
    exact Option.isSome_iff_exists.mp (hA1 _).1
  have hL : ∀ (M : ℝ) (f : ℕ → Bool), ∃ L, (r2 P2 d B2 M f).output = some L := by
    intro M f
    rw [r2_eq]
    exact Option.isSome_iff_exists.mp (hB1 M _).1
  -- the composite run on a tape
  have hrun : ∀ t : Fin B → Bool, ∀ z L : ℝ,
      (r1 P1 d B1 (extendTape t)).output = some z →
      (r2 P2 d B2 z (fun j => extendTape t ((r1 P1 d B1 (extendTape t)).coins + j))).output = some L →
      (run Q Finset.univ d t B).output = some (dec e z L) ∧
      (run Q Finset.univ d t B).queries = (r1 P1 d B1 (extendTape t)).queries +
        (r2 P2 d B2 z (fun j => extendTape t ((r1 P1 d B1 (extendTape t)).coins + j))).queries := by
    intro t z L h1 h2
    obtain ⟨Tq, hTq, hout, hq⟩ := composite_run e P1 P2 d B1 B2 (extendTape t) z L h1 h2
    have key : (step Q d (extendTape t))^[B] (initState (Finset.univ : Finset (Fin n))) =
        (step Q d (extendTape t))^[Tq] (initState (Finset.univ : Finset (Fin n))) := by
      have h := Function.iterate_add_apply (step Q d (extendTape t)) (B - Tq) Tq
        (initState (Finset.univ : Finset (Fin n)))
      rw [Nat.sub_add_cancel (by omega)] at h
      rw [h, iterate_halted _ _ _ _ _ hout]
    unfold run
    rw [key]
    exact ⟨hout, hq⟩
  have hr1q : ∀ f, ((r1 P1 d B1 f).queries : ℝ) ≤ |CA| * ((n : ℝ) + 1) ^ (2 - εq) := by
    intro f; rw [r1_eq]; exact hqA _
  have hr2q : ∀ M f, ((r2 P2 d B2 M f).queries : ℝ) ≤ |CB| * ((n : ℝ) + 1) ^ (2 - εq) := by
    intro M f; rw [r2_eq]; exact hqB M _
  constructor
  · intro t
    obtain ⟨z, h1⟩ := hz (extendTape t)
    obtain ⟨L, h2⟩ := hL z (fun j => extendTape t ((r1 P1 d B1 (extendTape t)).coins + j))
    obtain ⟨ho, hq⟩ := hrun t z L h1 h2
    refine ⟨by rw [ho]; rfl, ?_⟩
    rw [hq]; push_cast
    have := hr1q (extendTape t)
    have := hr2q z (fun j => extendTape t ((r1 P1 d B1 (extendTape t)).coins + j))
    have h0 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (2 - εq) := by positivity
    nlinarith [abs_nonneg CA, abs_nonneg CB]
  · -- probability
    set M := DoublingMST.mstWeight d with hM
    set K := cutLP d Finset.univ with hK
    obtain ⟨h32a, h32b⟩ := claim_3_2 d hd
    obtain ⟨h33a, h33b⟩ := claim_3_3 d hd
    have hM0 : 0 ≤ M := by linarith
    let g : (ℕ → Bool) → ℕ × ℝ := fun f => ((r1 P1 d B1 f).coins, ((r1 P1 d B1 f).output).getD 0)
    have hgk : ∀ f, (g f).1 ≤ B1 := by
      intro f
      have := coins_le P1 d f (initState (Finset.univ : Finset (Fin n))) B1
      have h0 : (initState (Finset.univ : Finset (Fin n))).coins = 0 := rfl
      simp only [g, r1]; omega
    have hgdet : ∀ f f', (∀ j < (g f).1, f j = f' j) → g f' = g f := by
      intro f f' h
      have : r1 P1 d B1 f = r1 P1 d B1 f' := iterate_congr_tape P1 d f f' _ B1 h
      simp only [g, this]
    let G1 : ℝ → Prop := fun a => M ≤ a ∧ a ≤ (1 + (e : ℝ) / 4) * M
    let G2 : ℝ → (Fin B2 → Bool) → Prop := fun a σ => ∃ L : ℝ,
      (runWithEstimate P2 d a σ B2).output = some L ∧ 0 ≤ L ∧ L ≤ K ∧
        (M - K ≤ ε * M → (1 + ε) / 2 * a ≤ L)
    have h1 : (5 / 6 : ℝ) * 2 ^ B1 ≤
        ((Finset.univ.filter (fun τ : Fin B1 → Bool => G1 (g (extendTape τ)).2)).card : ℝ) := by
      refine hA2.trans ?_
      refine Nat.cast_le.mpr (Finset.card_le_card ?_)
      intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      obtain ⟨z, hzτ, hz1, hz2⟩ := hτ
      have : (r1 P1 d B1 (extendTape τ)).output = some z := hzτ
      simp only [g, G1, this, Option.getD_some]
      exact ⟨hz1, hz2⟩
    have h2 : ∀ a, G1 a → (5 / 6 : ℝ) * 2 ^ B2 ≤
        ((Finset.univ.filter (fun σ : Fin B2 → Bool => G2 a σ)).card : ℝ) := by
      intro a ha
      have ha2 : a ≤ (1 + ε / 4) * M := ha.2.trans (by nlinarith)
      exact hB2 a ha.1 ha2
    have hcount := MTSPCount.compose_count B B1 B2 hB12 g hgk hgdet G1 G2 (by convert h1)
      (fun a ha => by convert h2 a ha)
    refine hcount.trans ?_
    refine Nat.cast_le.mpr (Finset.card_le_card ?_)
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    obtain ⟨hG1, L, hLout, hL0, hLK, hLD⟩ := ht
    obtain ⟨z, hz1⟩ := hz (extendTape t)
    have hgz : (g (extendTape t)).2 = z := by simp only [g, hz1, Option.getD_some]
    have hgk' : (g (extendTape t)).1 = (r1 P1 d B1 (extendTape t)).coins := rfl
    rw [hgz] at hG1 hLD hLout
    rw [hgk'] at hLout
    have hr2 : (r2 P2 d B2 z (fun j => extendTape t ((r1 P1 d B1 (extendTape t)).coins + j))).output
        = some L := by rw [r2_eq]; exact hLout
    obtain ⟨ho, -⟩ := hrun t z L hz1 hr2
    refine ⟨dec e z L, ho, ?_⟩
    have hLD' : M - K ≤ (e : ℝ) * M → (1 + (e : ℝ)) / 2 * z ≤ L := by
      intro hD
      have := hLD (hD.trans (mul_le_mul_of_nonneg_right he2.le hM0))
      have hz0 : 0 ≤ z := hM0.trans hG1.1
      have h3 : (1 + (e : ℝ)) / 2 * z ≤ (1 + ε) / 2 * z :=
        mul_le_mul_of_nonneg_right (by linarith) hz0
      exact h3.trans this
    have hdr := theorem_1_decision_rule M K (MetricTSP.tspOpt d) z L (e : ℝ) ⟨he0, by linarith⟩ hM0
      h33a h33b hG1 ⟨hL0, hLK⟩ hLD'
    simp only [dec]
    push_cast
    exact hdr

end MTSPThm1


open MetricTSPSublinear

theorem solution :
    ∃ (ε δ γ : ℝ) (P : SublinearSteiner.Program) (C : ℝ), 0 < ε ∧ 0 < δ ∧ 0 < γ ∧
      SublinearSteiner.Admissible P ∧
      ∀ (n : ℕ) (d : Fin n → Fin n → ℝ), DoublingMST.IsMetric d →
        (∀ tape : Fin ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ → Bool,
            (SublinearSteiner.run P Finset.univ d tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).output.isSome ∧
            ((SublinearSteiner.run P Finset.univ d tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).queries : ℝ) ≤
              C * ((n : ℝ) + 1) ^ (2 - ε)) ∧
        (2 / 3 : ℝ) * 2 ^ ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ ≤
          ((Finset.univ.filter (fun tape : Fin ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ → Bool => ∃ z : ℝ,
              (SublinearSteiner.run P Finset.univ d tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).output = some z ∧
              MetricTSP.tspOpt d ≤ z ∧ z ≤ (2 - δ) * MetricTSP.tspOpt d)).card : ℝ) :=
  MTSPThm1.theorem_1_sol
