-- Prove2me | solution 1 for ITPIRPreproc.MatchVec.WordRAM.wordLengthProgram_correct
-- status  : ACCEPTED   (prove)
-- author  : @Jesko
-- created : 2026-11-13T18:32:01.051218+00:00
-- url     : https://prove2.me/submissions/c394685c-b499-43b9-9fcc-984b3e412bf1

import Definitions.Def_ITPIRPreproc_MatchVec_RAMParameters
import Definitions.Def_ITPIRPreproc_MatchVec_PolynomialParameters
import Mathlib.Tactic
open ITPIRPreproc.MatchVec ITPIRPreproc.MatchVec.WordRAM ITPIRPreproc.MatchVec.PolynomialConstruction

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000


set_option backward.isDefEq.respectTransparency false

namespace ITPIRPreproc.MatchVec.WordRAM

def eraseCost (s : State) : State := {s with cost := 0}

noncomputable def shapeStep (P : Program) (inp : List Bool) (ω : ℕ → Bool) (s : State) : State :=
  eraseCost (step P inp ω s)

@[simp] theorem eraseCost_idem (s : State) : eraseCost (eraseCost s) = eraseCost s := rfl

theorem eraseCost_step (P : Program) (inp : List Bool) (ω : ℕ → Bool) (s : State) :
    eraseCost (step P inp ω s) = eraseCost (step P inp ω (eraseCost s)) := by
  unfold step
  by_cases hs : s.halted = true
  · simp [hs, eraseCost]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, eraseCost]
    cases hf : P[s.pc]? with
    | none => rfl
    | some op => cases op <;> rfl

theorem eraseCost_iterate (P : Program) (inp : List Bool) (ω : ℕ → Bool)
    (s : State) (k : ℕ) :
    eraseCost ((step P inp ω)^[k] s) = (shapeStep P inp ω)^[k] (eraseCost s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    exact eraseCost_step P inp ω _

theorem run_shape (P : Program) (inp : List Bool) (ω : ℕ → Bool) (k : ℕ) :
    eraseCost (run P inp ω k) = (shapeStep P inp ω)^[k] initState :=
  eraseCost_iterate P inp ω initState k

theorem step_of_halted (P : Program) (inp : List Bool) (ω : ℕ → Bool)
    (s : State) (hs : s.halted = true) : step P inp ω s = s := by
  simp [step, hs]

theorem run_succ (P : Program) (inp : List Bool) (ω : ℕ → Bool) (k : ℕ) :
    run P inp ω (k+1) = step P inp ω (run P inp ω k) :=
  Function.iterate_succ_apply' _ _ _

theorem run_add (P : Program) (inp : List Bool) (ω : ℕ → Bool) (a b : ℕ) :
    run P inp ω (a+b) = (step P inp ω)^[b] (run P inp ω a) := by
  simp only [run, Nat.add_comm a b, Function.iterate_add_apply]

theorem run_stable (P : Program) (inp : List Bool) (ω : ℕ → Bool) (k : ℕ)
    (hk : (run P inp ω k).halted = true) (j : ℕ) :
    run P inp ω (k+j) = run P inp ω k := by
  rw [run_add]
  exact Function.iterate_fixed (step_of_halted P inp ω _ hk) j

theorem haltStep_le (P : Program) (inp : List Bool) (ω : ℕ → Bool) (k : ℕ)
    (hk : (run P inp ω k).halted = true) : haltStep P inp ω ≤ k := by
  have hh : ∃ j, (run P inp ω j).halted = true := ⟨k, hk⟩
  simp only [haltStep, dif_pos hh]
  exact Nat.find_min' hh hk

theorem finalState_eq_run (P : Program) (inp : List Bool) (ω : ℕ → Bool) (k : ℕ)
    (hk : (run P inp ω k).halted = true) : finalState P inp ω = run P inp ω k := by
  have hh : ∃ j, (run P inp ω j).halted = true := ⟨k, hk⟩
  have hhalt : (run P inp ω (haltStep P inp ω)).halted = true := by
    simp only [haltStep, dif_pos hh]
    exact Nat.find_spec hh
  have hle := haltStep_le P inp ω k hk
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
  rw [hj]
  exact (run_stable P inp ω _ hhalt j).symm

theorem cost_eq_run (P : Program) (inp : List Bool) (ω : ℕ → Bool) (k : ℕ)
    (hk : (run P inp ω k).halted = true) : cost P inp ω = (run P inp ω k).cost := by
  unfold cost
  rw [finalState_eq_run P inp ω k hk]

theorem output_eq_run (P : Program) (inp : List Bool) (ω : ℕ → Bool) (k : ℕ)
    (hk : (run P inp ω k).halted = true) : output P inp ω = (run P inp ω k).out := by
  unfold output
  rw [finalState_eq_run P inp ω k hk]

theorem workingBits_le_of_trace (P : Program) (inp : List Bool) (ω : ℕ → Bool)
    (k B : ℕ) (hk : (run P inp ω k).halted = true)
    (hb : ∀ j ≤ k, space (run P inp ω j) ≤ B) : workingBits P inp ω ≤ B := by
  unfold workingBits
  apply Finset.sup_le
  intro j hj
  exact hb j (le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    (haltStep_le P inp ω k hk))

theorem words_le_size (w x : ℕ) (hw : 1 ≤ w) : words w x ≤ Nat.size x := by
  unfold words
  apply (Nat.div_le_iff_le_mul_add_pred (by omega)).mpr
  have hm : Nat.size x ≤ w * Nat.size x := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (Nat.size x) hw
  omega

theorem wordSize_pos (inp : List Bool) (s : State) : 1 ≤ wordSize inp s :=
  le_max_left _ _

theorem step_cost_bound (P : Program) (inp : List Bool) (ω : ℕ → Bool)
    (s : State) (B : ℕ)
    (hr : ∀ i, Nat.size (s.regs i) ≤ B)
    (hm : ∀ i, Nat.size (s.mem i) ≤ B)
    (hc : ∀ d k, Instr.const d k ∈ P → Nat.size k ≤ B) :
    (step P inp ω s).cost ≤ s.cost + (1+2*B) := by
  have hwr (i : ℕ) : words (wordSize inp s) (s.regs i) ≤ B :=
    (words_le_size _ _ (wordSize_pos inp s)).trans (hr i)
  have hwm (i : ℕ) : words (wordSize inp s) (s.mem i) ≤ B :=
    (words_le_size _ _ (wordSize_pos inp s)).trans (hm i)
  by_cases hs : s.halted = true
  · rw [step_of_halted P inp ω s hs]
    omega
  · cases hf : P[s.pc]? with
    | none => simp [step, hs, hf]
    | some op =>
      have hop : op ∈ P := List.mem_of_getElem? hf
      cases op with
      | const d k =>
        have hwk := (words_le_size (wordSize inp s) k (wordSize_pos inp s)).trans (hc d k hop)
        simp only [step, hs, Bool.false_eq_true, ↓reduceIte, hf]
        omega
      | _ => simp only [step, hs, Bool.false_eq_true, ↓reduceIte, hf] <;>
        grind only

theorem space_le_of_registers (s : State) (R B : ℕ)
    (hmem : s.mem = 0) (hout : s.out = [])
    (hsupp : s.regs.support ⊆ Finset.range R)
    (hbits : ∀ r, Nat.size (s.regs r) ≤ B) : space s ≤ R*B := by
  simp only [space, hmem, hout, Finsupp.sum_zero_index, List.length_nil, add_zero]
  unfold Finsupp.sum
  calc
    _ ≤ ∑ r ∈ s.regs.support, B := Finset.sum_le_sum (fun r _ => hbits r)
    _ = s.regs.support.card * B := by simp
    _ ≤ R*B := Nat.mul_le_mul_right B (by simpa using Finset.card_le_card hsupp)

theorem cost_le_of_step_bound (P : Program) (inp : List Bool) (ω : ℕ → Bool)
    (k M : ℕ) (hb : ∀ j < k,
      (step P inp ω (run P inp ω j)).cost ≤ (run P inp ω j).cost + M) :
    (run P inp ω k).cost ≤ k*M := by
  induction k with
  | zero => simp [run, initState]
  | succ k ih =>
    rw [run_succ]
    have hp := ih (fun j hj => hb j (by omega))
    have hq := hb k (by omega)
    nlinarith

end ITPIRPreproc.MatchVec.WordRAM

namespace ITPIRPreproc.MatchVec.WordRAM.ReadNatProof

def value : List Bool → ℕ := List.foldr Nat.bit 0

@[simp] theorem value_nil : value [] = 0 := rfl
@[simp] theorem value_cons (b : Bool) (bs : List Bool) :
    value (b::bs) = b.toNat + 2*value bs := by simp [value, Nat.bit_val]; omega

theorem value_bits (n : ℕ) : value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn, value_cons, ih]
    simp [Nat.bit_val, Nat.add_comm]

noncomputable def regs (a w f t : ℕ) : ℕ →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 w + Finsupp.single 2 f +
    Finsupp.single 3 t + Finsupp.single 4 1

@[simp] theorem regs_zero (a w f t : ℕ) : regs a w f t 0 = a := by simp [regs]
@[simp] theorem regs_one (a w f t : ℕ) : regs a w f t 1 = w := by simp [regs]
@[simp] theorem regs_two (a w f t : ℕ) : regs a w f t 2 = f := by simp [regs]
@[simp] theorem regs_three (a w f t : ℕ) : regs a w f t 3 = t := by simp [regs]
@[simp] theorem regs_four (a w f t : ℕ) : regs a w f t 4 = 1 := by simp [regs]

theorem regs_ge_five (a w f t i : ℕ) (hi : 5 ≤ i) : regs a w f t i = 0 := by
  simp only [regs, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> omega

@[simp] theorem regs_five (a w f t : ℕ) : regs a w f t 5 = 0 := regs_ge_five _ _ _ _ _ le_rfl

@[simp] theorem regs_update_zero (a w f t v : ℕ) : (regs a w f t).update 0 v = regs v w f t := by
  ext i
  by_cases hi : i < 5
  · interval_cases i <;> simp [Finsupp.update_apply]
  · simp [Finsupp.update_apply, show i ≠ 0 by omega, regs_ge_five _ _ _ _ i (by omega)]

@[simp] theorem regs_update_one (a w f t v : ℕ) : (regs a w f t).update 1 v = regs a v f t := by
  ext i
  by_cases hi : i < 5
  · interval_cases i <;> simp [Finsupp.update_apply]
  · simp [Finsupp.update_apply, show i ≠ 1 by omega, regs_ge_five _ _ _ _ i (by omega)]

@[simp] theorem regs_update_two (a w f t v : ℕ) : (regs a w f t).update 2 v = regs a w v t := by
  ext i
  by_cases hi : i < 5
  · interval_cases i <;> simp [Finsupp.update_apply]
  · simp [Finsupp.update_apply, show i ≠ 2 by omega, regs_ge_five _ _ _ _ i (by omega)]

@[simp] theorem regs_update_three (a w f t v : ℕ) : (regs a w f t).update 3 v = regs a w f v := by
  ext i
  by_cases hi : i < 5
  · interval_cases i <;> simp [Finsupp.update_apply]
  · simp [Finsupp.update_apply, show i ≠ 3 by omega, regs_ge_five _ _ _ _ i (by omega)]

noncomputable def state (pc pos a w f t : ℕ) (halted : Bool := false) : State :=
  ⟨pc, regs a w f t, 0, pos, [], 0, halted, 0⟩

def Bounded (R : ℕ) (s : State) : Prop :=
  s.mem = 0 ∧ s.out = [] ∧ s.regs.support ⊆ Finset.range 5 ∧ ∀ i, s.regs i ≤ R

theorem bounded_state (R pc pos a w f t : ℕ) (halted : Bool)
    (hR : 1 ≤ R) (ha : a ≤ R) (hw : w ≤ R) (hf : f ≤ R) (ht : t ≤ R) :
    Bounded R (state pc pos a w f t halted) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro i hi
    by_contra hn
    have hig : 5 ≤ i := by simpa using hn
    have hz : (state pc pos a w f t halted).regs i = 0 := regs_ge_five _ _ _ _ _ hig
    exact (Finsupp.mem_support_iff.mp hi) hz
  · intro i
    change regs a w f t i ≤ R
    by_cases hi : i < 5
    · interval_cases i <;> simp_all
    · rw [regs_ge_five _ _ _ _ i (by omega)]
      omega

theorem trace_append {α : Type*} (f : α → α) (Q : α → Prop) (s : α) (a b : ℕ)
    (ha : ∀ j ≤ a, Q (f^[j] s)) (hb : ∀ j ≤ b, Q (f^[j] (f^[a] s))) :
    ∀ j ≤ a+b, Q (f^[j] s) := by
  intro j hj
  by_cases hja : j ≤ a
  · exact ha j hja
  · have hab : a ≤ j := by omega
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [Nat.add_comm a r, Function.iterate_add_apply]
    exact hb r (by omega)

theorem encNat_length (n : ℕ) : (encNat n).length = 2*n.size+1 := by
  simp [encNat, List.length_flatMap, Nat.size_eq_bits_len, Nat.mul_comm]


end ITPIRPreproc.MatchVec.WordRAM.ReadNatProof


set_option backward.isDefEq.respectTransparency false

namespace ITPIRPreproc.MatchVec.WordRAM

@[simp] theorem relocate_space (offset : ℕ) (s : State) :
    space (relocateState offset s) = space s := rfl

@[simp] theorem relocate_wordSize (inp : List Bool) (offset : ℕ) (s : State) :
    wordSize inp (relocateState offset s) = wordSize inp s := rfl

theorem relocate_fetch (precode P : Program) (pc : ℕ) :
    (placeAfter precode P)[precode.length+pc]? = (P[pc]?).map (relocateInstr precode.length) := by
  unfold placeAfter
  rw [List.getElem?_append_right (by omega)]
  simp

theorem relocate_step (precode P : Program) (inp : List Bool) (ω : ℕ → Bool) (s : State) :
    step (placeAfter precode P) inp ω (relocateState precode.length s) =
      relocateState precode.length (step P inp ω s) := by
  by_cases hs : s.halted = true
  · simp [step, relocateState, hs]
  · unfold step
    simp only [relocateState, hs, Bool.false_eq_true, ↓reduceIte]
    rw [relocate_fetch]
    cases hf : P[s.pc]? with
    | none => rfl
    | some op =>
      cases op <;> simp [relocateInstr, Nat.add_assoc, wordSize, space]
      split_ifs <;> rfl

theorem relocate_deterministic (precode P : Program) :
    Deterministic (placeAfter precode P) ↔ Deterministic precode ∧ Deterministic P := by
  constructor
  · intro h
    constructor
    · intro op hop d
      exact h op (List.mem_append_left _ hop) d
    · intro op hop d hc
      apply h (.coin d) _ d rfl
      apply List.mem_append_right
      apply List.mem_map.mpr
      exact ⟨op, hop, by simp [hc, relocateInstr]⟩
  · rintro ⟨ha,hb⟩ op hop d
    rcases List.mem_append.mp hop with hop | hop
    · exact ha op hop d
    · obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hop
      have hx := hb old hold d
      cases old <;> simp_all [relocateInstr]

theorem relocate_streaming (precode P : Program) :
    Streaming (placeAfter precode P) ↔ Streaming precode ∧ Streaming P := by
  constructor
  · intro h
    constructor
    · intro op hop d a
      exact h op (List.mem_append_left _ hop) d a
    · intro op hop d a hc
      apply h (.inBitAt d a) _ d a rfl
      apply List.mem_append_right
      apply List.mem_map.mpr
      exact ⟨op, hop, by simp [hc, relocateInstr]⟩
  · rintro ⟨ha,hb⟩ op hop d a
    rcases List.mem_append.mp hop with hop | hop
    · exact ha op hop d a
    · obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hop
      have hx := hb old hold d a
      cases old <;> simp_all [relocateInstr]

theorem relocate_execution (precode P : Program) (inp : List Bool) (ω : ℕ → Bool)
    (s : State) (k : ℕ) :
    (step (placeAfter precode P) inp ω)^[k] (relocateState precode.length s) =
      relocateState precode.length ((step P inp ω)^[k] s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, relocate_step]

end ITPIRPreproc.MatchVec.WordRAM


set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000

namespace ITPIRPreproc.MatchVec.WordRAM.ParameterProof
open PolynomialConstruction

noncomputable def regs (r0 r1 r2 r3 r4 r5 r6 r7 : ℕ) : ℕ →₀ ℕ :=
  Finsupp.single 0 r0 +
    Finsupp.single 1 r1 +
    Finsupp.single 2 r2 +
    Finsupp.single 3 r3 +
    Finsupp.single 4 r4 +
    Finsupp.single 5 r5 +
    Finsupp.single 6 r6 +
    Finsupp.single 7 r7

@[simp] theorem regs_0 (r0 r1 r2 r3 r4 r5 r6 r7 : ℕ) : regs r0 r1 r2 r3 r4 r5 r6 r7 0 = r0 := by simp [regs]
@[simp] theorem regs_1 (r0 r1 r2 r3 r4 r5 r6 r7 : ℕ) : regs r0 r1 r2 r3 r4 r5 r6 r7 1 = r1 := by simp [regs]
@[simp] theorem regs_2 (r0 r1 r2 r3 r4 r5 r6 r7 : ℕ) : regs r0 r1 r2 r3 r4 r5 r6 r7 2 = r2 := by simp [regs]
@[simp] theorem regs_3 (r0 r1 r2 r3 r4 r5 r6 r7 : ℕ) : regs r0 r1 r2 r3 r4 r5 r6 r7 3 = r3 := by simp [regs]
@[simp] theorem regs_4 (r0 r1 r2 r3 r4 r5 r6 r7 : ℕ) : regs r0 r1 r2 r3 r4 r5 r6 r7 4 = r4 := by simp [regs]
@[simp] theorem regs_5 (r0 r1 r2 r3 r4 r5 r6 r7 : ℕ) : regs r0 r1 r2 r3 r4 r5 r6 r7 5 = r5 := by simp [regs]
@[simp] theorem regs_6 (r0 r1 r2 r3 r4 r5 r6 r7 : ℕ) : regs r0 r1 r2 r3 r4 r5 r6 r7 6 = r6 := by simp [regs]
@[simp] theorem regs_7 (r0 r1 r2 r3 r4 r5 r6 r7 : ℕ) : regs r0 r1 r2 r3 r4 r5 r6 r7 7 = r7 := by simp [regs]
theorem regs_ge (r0 r1 r2 r3 r4 r5 r6 r7 i : ℕ) (hi : 8 ≤ i) : regs r0 r1 r2 r3 r4 r5 r6 r7 i = 0 := by
  simp only [regs, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> omega

@[simp] theorem update_0 (r0 r1 r2 r3 r4 r5 r6 r7 v : ℕ) :
    (regs r0 r1 r2 r3 r4 r5 r6 r7).update 0 v = regs v r1 r2 r3 r4 r5 r6 r7 := by
  ext j
  by_cases hj : j < 8
  · interval_cases j <;> simp [Finsupp.update_apply]
  · simp [Finsupp.update_apply, show j ≠ 0 by omega, regs_ge _ _ _ _ _ _ _ _ j (by omega)]

@[simp] theorem update_1 (r0 r1 r2 r3 r4 r5 r6 r7 v : ℕ) :
    (regs r0 r1 r2 r3 r4 r5 r6 r7).update 1 v = regs r0 v r2 r3 r4 r5 r6 r7 := by
  ext j
  by_cases hj : j < 8
  · interval_cases j <;> simp [Finsupp.update_apply]
  · simp [Finsupp.update_apply, show j ≠ 1 by omega, regs_ge _ _ _ _ _ _ _ _ j (by omega)]

@[simp] theorem update_2 (r0 r1 r2 r3 r4 r5 r6 r7 v : ℕ) :
    (regs r0 r1 r2 r3 r4 r5 r6 r7).update 2 v = regs r0 r1 v r3 r4 r5 r6 r7 := by
  ext j
  by_cases hj : j < 8
  · interval_cases j <;> simp [Finsupp.update_apply]
  · simp [Finsupp.update_apply, show j ≠ 2 by omega, regs_ge _ _ _ _ _ _ _ _ j (by omega)]

@[simp] theorem update_3 (r0 r1 r2 r3 r4 r5 r6 r7 v : ℕ) :
    (regs r0 r1 r2 r3 r4 r5 r6 r7).update 3 v = regs r0 r1 r2 v r4 r5 r6 r7 := by
  ext j
  by_cases hj : j < 8
  · interval_cases j <;> simp [Finsupp.update_apply]
  · simp [Finsupp.update_apply, show j ≠ 3 by omega, regs_ge _ _ _ _ _ _ _ _ j (by omega)]

@[simp] theorem update_4 (r0 r1 r2 r3 r4 r5 r6 r7 v : ℕ) :
    (regs r0 r1 r2 r3 r4 r5 r6 r7).update 4 v = regs r0 r1 r2 r3 v r5 r6 r7 := by
  ext j
  by_cases hj : j < 8
  · interval_cases j <;> simp [Finsupp.update_apply]
  · simp [Finsupp.update_apply, show j ≠ 4 by omega, regs_ge _ _ _ _ _ _ _ _ j (by omega)]

@[simp] theorem update_5 (r0 r1 r2 r3 r4 r5 r6 r7 v : ℕ) :
    (regs r0 r1 r2 r3 r4 r5 r6 r7).update 5 v = regs r0 r1 r2 r3 r4 v r6 r7 := by
  ext j
  by_cases hj : j < 8
  · interval_cases j <;> simp [Finsupp.update_apply]
  · simp [Finsupp.update_apply, show j ≠ 5 by omega, regs_ge _ _ _ _ _ _ _ _ j (by omega)]

@[simp] theorem update_6 (r0 r1 r2 r3 r4 r5 r6 r7 v : ℕ) :
    (regs r0 r1 r2 r3 r4 r5 r6 r7).update 6 v = regs r0 r1 r2 r3 r4 r5 v r7 := by
  ext j
  by_cases hj : j < 8
  · interval_cases j <;> simp [Finsupp.update_apply]
  · simp [Finsupp.update_apply, show j ≠ 6 by omega, regs_ge _ _ _ _ _ _ _ _ j (by omega)]

@[simp] theorem update_7 (r0 r1 r2 r3 r4 r5 r6 r7 v : ℕ) :
    (regs r0 r1 r2 r3 r4 r5 r6 r7).update 7 v = regs r0 r1 r2 r3 r4 r5 r6 v := by
  ext j
  by_cases hj : j < 8
  · interval_cases j <;> simp [Finsupp.update_apply]
  · simp [Finsupp.update_apply, show j ≠ 7 by omega, regs_ge _ _ _ _ _ _ _ _ j (by omega)]

noncomputable def state (pc pos h u ell p c : ℕ) (halted : Bool := false) : State :=
  ⟨pc, regs h u ell p c 1 0 2, 0, pos, [], 0, halted, 0⟩

def Bounded (R : ℕ) (s : State) : Prop :=
  s.mem = 0 ∧ s.out = [] ∧ s.regs.support ⊆ Finset.range 8 ∧ ∀ i, s.regs i ≤ R

theorem bounded_state (R pc pos h u ell p c : ℕ) (halted : Bool)
    (hR : 2 ≤ R) (hh : h ≤ R) (hu : u ≤ R) (he : ell ≤ R)
    (hp : p ≤ R) (hc : c ≤ R) : Bounded R (state pc pos h u ell p c halted) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro i hi
    by_contra hn
    have hig : 8 ≤ i := by simpa using hn
    have hz : (state pc pos h u ell p c halted).regs i = 0 := regs_ge _ _ _ _ _ _ _ _ _ hig
    exact (Finsupp.mem_support_iff.mp hi) hz
  · intro i
    change regs h u ell p c 1 0 2 i ≤ R
    by_cases hi : i < 8
    · interval_cases i <;> simp_all <;> omega
    · rw [regs_ge _ _ _ _ _ _ _ _ i (by omega)]; omega

theorem step_7 (inp : List Bool) (ω : ℕ → Bool) (pos h u ell p c : ℕ) :
    shapeStep wordLengthCode inp ω (state 7 pos h u ell p c) =
      state (if c<h then 9 else 8) pos h u ell p c := by
  simp [shapeStep, eraseCost, step, wordLengthCode, state]

theorem step_8 (inp : List Bool) (ω : ℕ → Bool) (pos h u ell p c : ℕ) :
    shapeStep wordLengthCode inp ω (state 8 pos h u ell p c) =
      state 12 pos h u ell p c := by
  simp [shapeStep, eraseCost, step, wordLengthCode, state]

theorem step_9 (inp : List Bool) (ω : ℕ → Bool) (pos h u ell p c : ℕ) :
    shapeStep wordLengthCode inp ω (state 9 pos h u ell p c) =
      state 10 pos h (u*2) ell p c := by
  simp [shapeStep, eraseCost, step, wordLengthCode, state]

theorem step_10 (inp : List Bool) (ω : ℕ → Bool) (pos h u ell p c : ℕ) :
    shapeStep wordLengthCode inp ω (state 10 pos h u ell p c) =
      state 11 pos h u ell p (c+1) := by
  simp [shapeStep, eraseCost, step, wordLengthCode, state]

theorem step_11 (inp : List Bool) (ω : ℕ → Bool) (pos h u ell p c : ℕ) :
    shapeStep wordLengthCode inp ω (state 11 pos h u ell p c) =
      state 7 pos h u ell p c := by
  simp [shapeStep, eraseCost, step, wordLengthCode, state]

theorem step_12 (inp : List Bool) (ω : ℕ → Bool) (pos h u ell p c : ℕ) :
    shapeStep wordLengthCode inp ω (state 12 pos h u ell p c) =
      state 13 pos h u 0 p c := by
  simp [shapeStep, eraseCost, step, wordLengthCode, state]

theorem step_13 (inp : List Bool) (ω : ℕ → Bool) (pos h u ell p c : ℕ) :
    shapeStep wordLengthCode inp ω (state 13 pos h u ell p c) =
      state 14 pos h u ell 1 c := by
  simp [shapeStep, eraseCost, step, wordLengthCode, state]

theorem step_14 (inp : List Bool) (ω : ℕ → Bool) (pos h u ell p c : ℕ) :
    shapeStep wordLengthCode inp ω (state 14 pos h u ell p c) =
      state 15 pos h u ell p 0 := by
  simp [shapeStep, eraseCost, step, wordLengthCode, state]

theorem step_15 (inp : List Bool) (ω : ℕ → Bool) (pos h u ell p c : ℕ) :
    shapeStep wordLengthCode inp ω (state 15 pos h u ell p c) =
      state (if c<ell then 17 else 16) pos h u ell p c := by
  simp [shapeStep, eraseCost, step, wordLengthCode, state]

theorem step_16 (inp : List Bool) (ω : ℕ → Bool) (pos h u ell p c : ℕ) :
    shapeStep wordLengthCode inp ω (state 16 pos h u ell p c) =
      state 20 pos h u ell p c := by
  simp [shapeStep, eraseCost, step, wordLengthCode, state]

theorem step_17 (inp : List Bool) (ω : ℕ → Bool) (pos h u ell p c : ℕ) :
    shapeStep wordLengthCode inp ω (state 17 pos h u ell p c) =
      state 18 pos h u ell (p*ell) c := by
  simp [shapeStep, eraseCost, step, wordLengthCode, state]

theorem step_18 (inp : List Bool) (ω : ℕ → Bool) (pos h u ell p c : ℕ) :
    shapeStep wordLengthCode inp ω (state 18 pos h u ell p c) =
      state 19 pos h u ell p (c+1) := by
  simp [shapeStep, eraseCost, step, wordLengthCode, state]

theorem step_19 (inp : List Bool) (ω : ℕ → Bool) (pos h u ell p c : ℕ) :
    shapeStep wordLengthCode inp ω (state 19 pos h u ell p c) =
      state 15 pos h u ell p c := by
  simp [shapeStep, eraseCost, step, wordLengthCode, state]

theorem step_20 (inp : List Bool) (ω : ℕ → Bool) (pos h u ell p c : ℕ) :
    shapeStep wordLengthCode inp ω (state 20 pos h u ell p c) =
      state (if p<u then 22 else 21) pos h u ell p c := by
  simp [shapeStep, eraseCost, step, wordLengthCode, state]

theorem step_21 (inp : List Bool) (ω : ℕ → Bool) (pos h u ell p c : ℕ) :
    shapeStep wordLengthCode inp ω (state 21 pos h u ell p c) =
      state 22 pos h u ell p c true := by
  simp [shapeStep, eraseCost, step, wordLengthCode, state]

theorem step_22 (inp : List Bool) (ω : ℕ → Bool) (pos h u ell p c : ℕ) :
    shapeStep wordLengthCode inp ω (state 22 pos h u ell p c) =
      state 23 pos h u (ell+1) p c := by
  simp [shapeStep, eraseCost, step, wordLengthCode, state]

theorem step_23 (inp : List Bool) (ω : ℕ → Bool) (pos h u ell p c : ℕ) :
    shapeStep wordLengthCode inp ω (state 23 pos h u ell p c) =
      state 13 pos h u ell p c := by
  simp [shapeStep, eraseCost, step, wordLengthCode, state]

theorem exp_body (inp : List Bool) (ω : ℕ → Bool) (pos h u ell p c : ℕ)
    (hc : c<h) :
    (shapeStep wordLengthCode inp ω)^[4] (state 7 pos h u ell p c) =
      state 7 pos h (u*2) ell p (c+1) := by
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
    step_7, step_9, step_10, step_11, if_pos hc]

theorem exp_body_trace (inp : List Bool) (ω : ℕ → Bool) (R pos h u ell p c : ℕ)
    (hc : c<h) (hR : 2 ≤ R) (hh : h ≤ R) (hu : u*2 ≤ R) (he : ell ≤ R) (hp : p ≤ R) :
    ∀ j ≤ 4, Bounded R ((shapeStep wordLengthCode inp ω)^[j] (state 7 pos h u ell p c)) := by
  intro j hj
  interval_cases j <;>
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
      step_7, step_9, step_10, step_11, if_pos hc]
  all_goals apply bounded_state <;> omega

theorem pow_body (inp : List Bool) (ω : ℕ → Bool) (pos h u ell p c : ℕ)
    (hc : c<ell) :
    (shapeStep wordLengthCode inp ω)^[4] (state 15 pos h u ell p c) =
      state 15 pos h u ell (p*ell) (c+1) := by
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
    step_15, step_17, step_18, step_19, if_pos hc]

theorem pow_body_trace (inp : List Bool) (ω : ℕ → Bool) (R pos h u ell p c : ℕ)
    (hc : c<ell) (hR : 2 ≤ R) (hh : h ≤ R) (hu : u ≤ R) (he : ell ≤ R)
    (hp : p ≤ R) (hp' : p*ell ≤ R) :
    ∀ j ≤ 4, Bounded R ((shapeStep wordLengthCode inp ω)^[j] (state 15 pos h u ell p c)) := by
  intro j hj
  interval_cases j <;>
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
      step_15, step_17, step_18, step_19, if_pos hc]
  all_goals apply bounded_state <;> omega

theorem exp_loop (inp : List Bool) (ω : ℕ → Bool) (R pos h ell p c t : ℕ)
    (hct : c+t=h) (hR : 2 ≤ R) (hh : h ≤ R) (hu : 2^h ≤ R)
    (he : ell ≤ R) (hp : p ≤ R) :
    (shapeStep wordLengthCode inp ω)^[4*t+2] (state 7 pos h (2^c) ell p c) =
      state 12 pos h (2^h) ell p h ∧
    ∀ j ≤ 4*t+2, Bounded R
      ((shapeStep wordLengthCode inp ω)^[j] (state 7 pos h (2^c) ell p c)) := by
  induction t generalizing c with
  | zero =>
    have hc : c=h := by omega
    subst c
    constructor
    · norm_num [Function.iterate_succ_apply', step_7, step_8]
    · intro j hj
      interval_cases j <;>
        norm_num only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
          step_7, step_8, lt_self_iff_false, ↓reduceIte]
      all_goals apply bounded_state <;> assumption
  | succ t ih =>
    have hc : c<h := by omega
    have hpow : 2^(c+1) ≤ R := (Nat.pow_le_pow_right (by omega) (by omega)).trans hu
    obtain ⟨heq,ht⟩ := ih (c+1) (by omega)
    have hb := exp_body inp ω pos h (2^c) ell p c hc
    rw [← pow_succ] at hb
    constructor
    · rw [show 4*(t+1)+2=(4*t+2)+4 by omega, Function.iterate_add_apply, hb, heq]
    · have hfirst := exp_body_trace inp ω R pos h (2^c) ell p c hc hR hh
        (by simpa [pow_succ] using hpow) he hp
      have hlast : ∀ j ≤ 4*t+2, Bounded R
          ((shapeStep wordLengthCode inp ω)^[j]
            ((shapeStep wordLengthCode inp ω)^[4] (state 7 pos h (2^c) ell p c))) := by
        rw [hb]; exact ht
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ReadNatProof.trace_append (shapeStep wordLengthCode inp ω) (Bounded R)
          (state 7 pos h (2^c) ell p c) 4 (4*t+2) hfirst hlast

theorem pow_le_self (ell c : ℕ) (hc : c ≤ ell) : ell^c ≤ ell^ell := by
  by_cases he : ell=0
  · subst ell
    have hc0 : c=0 := by omega
    subst c
    rfl
  · exact Nat.pow_le_pow_right (by omega) hc

theorem pow_loop (inp : List Bool) (ω : ℕ → Bool) (R pos h u ell c t : ℕ)
    (hct : c+t=ell) (hR : 2 ≤ R) (hh : h ≤ R) (hu : u ≤ R)
    (he : ell ≤ R) (hp : ell^ell ≤ R) :
    (shapeStep wordLengthCode inp ω)^[4*t+2] (state 15 pos h u ell (ell^c) c) =
      state 20 pos h u ell (ell^ell) ell ∧
    ∀ j ≤ 4*t+2, Bounded R
      ((shapeStep wordLengthCode inp ω)^[j] (state 15 pos h u ell (ell^c) c)) := by
  induction t generalizing c with
  | zero =>
    have hc : c=ell := by omega
    subst c
    constructor
    · norm_num [Function.iterate_succ_apply', step_15, step_16]
    · intro j hj
      interval_cases j <;>
        norm_num only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
          step_15, step_16, lt_self_iff_false, ↓reduceIte]
      all_goals apply bounded_state <;> assumption
  | succ t ih =>
    have hc : c<ell := by omega
    have hpow : ell^(c+1) ≤ R := (pow_le_self ell (c+1) (by omega)).trans hp
    have hpow0 : ell^c ≤ R := (pow_le_self ell c (by omega)).trans hp
    obtain ⟨heq,ht⟩ := ih (c+1) (by omega)
    have hb := pow_body inp ω pos h u ell (ell^c) c hc
    rw [← pow_succ] at hb
    constructor
    · rw [show 4*(t+1)+2=(4*t+2)+4 by omega, Function.iterate_add_apply, hb, heq]
    · have hfirst := pow_body_trace inp ω R pos h u ell (ell^c) c hc hR hh hu he
        hpow0 (by simpa [pow_succ] using hpow)
      have hlast : ∀ j ≤ 4*t+2, Bounded R
          ((shapeStep wordLengthCode inp ω)^[j]
            ((shapeStep wordLengthCode inp ω)^[4] (state 15 pos h u ell (ell^c) c))) := by
        rw [hb]; exact ht
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ReadNatProof.trace_append (shapeStep wordLengthCode inp ω) (Bounded R)
          (state 15 pos h u ell (ell^c) c) 4 (4*t+2) hfirst hlast

theorem wordLength_spec (h : ℕ) : 2^h ≤ (wordLength h)^(wordLength h) := by
  unfold wordLength
  exact Nat.find_spec (p := fun ell : ℕ => 2^h ≤ ell^ell) _

theorem wordLength_min (h i : ℕ) (hi : i<wordLength h) : i^i<2^h := by
  unfold wordLength at hi
  exact Nat.lt_of_not_ge (Nat.find_min (p := fun t : ℕ => 2^h ≤ t^t) _ hi)

/-- Number of instructions used by the search starting at i with r unsuccessful candidates. -/
def searchTicks (i r : ℕ) : ℕ := 2*r^2+(4*i+9)*r+4*i+6

theorem searchTicks_succ (i r : ℕ) : searchTicks i (r+1) = searchTicks (i+1) r + (4*i+7) := by
  unfold searchTicks; ring

theorem candidate_run (inp : List Bool) (ω : ℕ → Bool) (R pos h u i p c : ℕ)
    (hR : 2 ≤ R) (hh : h ≤ R) (hu : u ≤ R) (hi : i ≤ R) (hp : p ≤ R) (hc : c ≤ R)
    (hpow : i^i ≤ R) :
    (shapeStep wordLengthCode inp ω)^[4*i+4] (state 13 pos h u i p c) =
      state 20 pos h u i (i^i) i ∧
    ∀ j ≤ 4*i+4, Bounded R
      ((shapeStep wordLengthCode inp ω)^[j] (state 13 pos h u i p c)) := by
  have hb : (shapeStep wordLengthCode inp ω)^[2] (state 13 pos h u i p c) =
      state 15 pos h u i 1 0 := by
    norm_num [Function.iterate_succ_apply', step_13, step_14]
  have hbtrace : ∀ j ≤ 2, Bounded R
      ((shapeStep wordLengthCode inp ω)^[j] (state 13 pos h u i p c)) := by
    intro j hj; interval_cases j <;>
      norm_num only [Function.iterate_succ_apply', Function.iterate_zero, id_eq, step_13, step_14]
    all_goals apply bounded_state <;> omega
  obtain ⟨heq,ht⟩ := pow_loop inp ω R pos h u i 0 i (by omega) hR hh hu hi hpow
  simp only [pow_zero] at heq ht
  constructor
  · rw [show 4*i+4=(4*i+2)+2 by omega, Function.iterate_add_apply, hb, heq]
  · have hlast : ∀ j ≤ 4*i+2, Bounded R
        ((shapeStep wordLengthCode inp ω)^[j]
          ((shapeStep wordLengthCode inp ω)^[2] (state 13 pos h u i p c))) := by
      rw [hb]; exact ht
    intro j hj
    exact ReadNatProof.trace_append (shapeStep wordLengthCode inp ω) (Bounded R)
      (state 13 pos h u i p c) 2 (4*i+2) hbtrace hlast j (by omega)

theorem search_loop (inp : List Bool) (ω : ℕ → Bool) (R pos h i r p c : ℕ)
    (hir : i+r=wordLength h) (hR : 2 ≤ R) (hh : h ≤ R) (hu : 2^h ≤ R)
    (hL : wordLength h ≤ R) (hp : p ≤ R) (hc : c ≤ R)
    (hpows : ∀ j ≤ wordLength h, j^j ≤ R) :
    (shapeStep wordLengthCode inp ω)^[searchTicks i r] (state 13 pos h (2^h) i p c) =
      state 22 pos h (2^h) (wordLength h) ((wordLength h)^(wordLength h)) (wordLength h) true ∧
    ∀ j ≤ searchTicks i r, Bounded R
      ((shapeStep wordLengthCode inp ω)^[j] (state 13 pos h (2^h) i p c)) := by
  induction r generalizing i p c with
  | zero =>
    have hi : i=wordLength h := by omega
    subst i
    obtain ⟨hb,hbt⟩ := candidate_run inp ω R pos h (2^h) (wordLength h) p c
      hR hh hu hL hp hc (hpows _ le_rfl)
    have hfinish : (shapeStep wordLengthCode inp ω)^[2]
        (state 20 pos h (2^h) (wordLength h) ((wordLength h)^(wordLength h)) (wordLength h)) =
        state 22 pos h (2^h) (wordLength h) ((wordLength h)^(wordLength h)) (wordLength h) true := by
      norm_num only [Function.iterate_succ_apply', Function.iterate_zero, id_eq, step_20,
        if_neg (Nat.not_lt.mpr (wordLength_spec h)), step_21]
    constructor
    · rw [show searchTicks (wordLength h) 0=2+(4*wordLength h+4) by simp [searchTicks]; omega,
        Function.iterate_add_apply, hb, hfinish]
    · have hlast : ∀ j ≤ 2, Bounded R
          ((shapeStep wordLengthCode inp ω)^[j]
            ((shapeStep wordLengthCode inp ω)^[4*wordLength h+4]
              (state 13 pos h (2^h) (wordLength h) p c))) := by
        rw [hb]
        intro j hj; interval_cases j <;>
          norm_num only [Function.iterate_succ_apply', Function.iterate_zero, id_eq, step_20,
            if_neg (Nat.not_lt.mpr (wordLength_spec h)), step_21]
        all_goals apply bounded_state <;> first | assumption | exact hpows _ le_rfl
      intro j hj
      exact ReadNatProof.trace_append (shapeStep wordLengthCode inp ω) (Bounded R)
        (state 13 pos h (2^h) (wordLength h) p c) (4*wordLength h+4) 2 hbt hlast j
        (by simp only [searchTicks, pow_zero, Nat.mul_zero, Nat.add_zero] at hj; omega)
  | succ r ih =>
    have hi : i<wordLength h := by omega
    have hiR : i ≤ R := by omega
    have hi1R : i+1 ≤ R := by omega
    have hpow := hpows i (by omega)
    obtain ⟨hb,hbt⟩ := candidate_run inp ω R pos h (2^h) i p c hR hh hu hiR hp hc hpow
    have hjump : (shapeStep wordLengthCode inp ω)^[3] (state 20 pos h (2^h) i (i^i) i) =
        state 13 pos h (2^h) (i+1) (i^i) i := by
      norm_num only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
        step_20, if_pos (wordLength_min h i hi), step_22, step_23]
    have hrun : (shapeStep wordLengthCode inp ω)^[4*i+7] (state 13 pos h (2^h) i p c) =
        state 13 pos h (2^h) (i+1) (i^i) i := by
      rw [show 4*i+7=3+(4*i+4) by omega, Function.iterate_add_apply, hb, hjump]
    have hshort : ∀ j ≤ 4*i+7, Bounded R
        ((shapeStep wordLengthCode inp ω)^[j] (state 13 pos h (2^h) i p c)) := by
      have hlast : ∀ j ≤ 3, Bounded R
          ((shapeStep wordLengthCode inp ω)^[j]
            ((shapeStep wordLengthCode inp ω)^[4*i+4] (state 13 pos h (2^h) i p c))) := by
        rw [hb]
        intro j hj; interval_cases j <;>
          norm_num only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
            step_20, if_pos (wordLength_min h i hi), step_22, step_23]
        all_goals apply bounded_state <;> assumption
      intro j hj
      exact ReadNatProof.trace_append (shapeStep wordLengthCode inp ω) (Bounded R)
        (state 13 pos h (2^h) i p c) (4*i+4) 3 hbt hlast j (by omega)
    obtain ⟨heq,ht⟩ := ih (i+1) (i^i) i (by omega) hpow hiR
    constructor
    · rw [searchTicks_succ, Function.iterate_add_apply, hrun, heq]
    · have hlast : ∀ j ≤ searchTicks (i+1) r, Bounded R
          ((shapeStep wordLengthCode inp ω)^[j]
            ((shapeStep wordLengthCode inp ω)^[4*i+7] (state 13 pos h (2^h) i p c))) := by
        rw [hrun]; exact ht
      rw [searchTicks_succ, Nat.add_comm]
      exact ReadNatProof.trace_append (shapeStep wordLengthCode inp ω) (Bounded R)
        (state 13 pos h (2^h) i p c) (4*i+7) (searchTicks (i+1) r) hshort hlast

theorem wordLength_le (h : ℕ) : wordLength h ≤ h+2 := by
  unfold wordLength
  apply Nat.find_min'
  calc
    2^h ≤ (h+2)^h := Nat.pow_le_pow_left (by omega) _
    _ ≤ (h+2)^(h+2) := Nat.pow_le_pow_right (by omega) (by omega)

def bitCap (h : ℕ) : ℕ := (h+2)^2
def valueCap (h : ℕ) : ℕ := 2^bitCap h

theorem cap_bounds (h : ℕ) :
    2 ≤ valueCap h ∧ h+2 ≤ valueCap h ∧ 2^h ≤ valueCap h ∧
    2^h.size ≤ valueCap h ∧ ∀ i ≤ wordLength h, i^i ≤ valueCap h := by
  have he : h+2 ≤ bitCap h := by unfold bitCap; nlinarith
  have hh : h+2 ≤ valueCap h := by
    apply le_trans (Nat.le_of_lt (Nat.lt_two_pow_self (n := h+2)))
    exact Nat.pow_le_pow_right (by omega) he
  have hs : h.size ≤ h+2 := Nat.size_le.mpr (by
    exact (Nat.lt_two_pow_self (n := h)).trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
  refine ⟨by omega, hh, Nat.pow_le_pow_right (by omega) (by omega),
    Nat.pow_le_pow_right (by omega) (by omega), ?_⟩
  intro i hi
  have hi' : i ≤ h+2 := hi.trans (wordLength_le h)
  calc
    i^i ≤ (h+2)^i := Nat.pow_le_pow_left hi' _
    _ ≤ (h+2)^(h+2) := Nat.pow_le_pow_right (by omega) hi'
    _ ≤ (2^(h+2))^(h+2) := Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n := h+2))) _
    _ = valueCap h := by simp [← pow_mul, valueCap, bitCap, pow_two]

theorem initial_run (inp : List Bool) (ω : ℕ → Bool) (pos h w t : ℕ) :
    (shapeStep wordLengthCode inp ω)^[7] (ReadNatProof.state 0 pos h w 0 t) =
      state 7 pos h 1 0 1 0 := by
  simp [Function.iterate_succ_apply', shapeStep, eraseCost, step, wordLengthCode,
    ReadNatProof.state, state, ReadNatProof.regs, regs]
  ext i
  by_cases hi : i<8
  · interval_cases i <;> simp [Finsupp.update_apply, Finsupp.single_apply]
  · simp [Finsupp.update_apply, Finsupp.single_apply, show i ≠ 0 by omega,
      show i ≠ 1 by omega, show i ≠ 2 by omega, show i ≠ 3 by omega,
      show i ≠ 4 by omega, show i ≠ 5 by omega, show i ≠ 6 by omega, show i ≠ 7 by omega,
      show 0 ≠ i by omega, show 1 ≠ i by omega, show 2 ≠ i by omega, show 3 ≠ i by omega,
      show 4 ≠ i by omega, show 5 ≠ i by omega, show 6 ≠ i by omega, show 7 ≠ i by omega]

theorem bounded_of_values (R : ℕ) (s : State) (hm : s.mem=0) (ho : s.out=[])
    (hz : ∀ i, 8 ≤ i → s.regs i=0) (hv : ∀ i, s.regs i ≤ R) : Bounded R s := by
  refine ⟨hm,ho,?_,hv⟩
  intro i hi
  by_contra hn
  have hig : 8 ≤ i := by simpa using hn
  exact (Finsupp.mem_support_iff.mp hi) (hz i hig)

theorem initial_trace (inp : List Bool) (ω : ℕ → Bool) (R pos h w t : ℕ)
    (hR : 2 ≤ R) (hh : h ≤ R) (hw : w ≤ R) (ht : t ≤ R) :
    ∀ j ≤ 7, Bounded R ((shapeStep wordLengthCode inp ω)^[j] (ReadNatProof.state 0 pos h w 0 t)) := by
  intro j hj
  interval_cases j <;>
    simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
      shapeStep, eraseCost, step, wordLengthCode, ReadNatProof.state, Bool.false_eq_true,
      ↓reduceIte, List.getElem?_cons_zero, List.getElem?_cons_succ]
  all_goals
    apply bounded_of_values _ _ rfl rfl
    · intro i hi
      simp [ReadNatProof.regs, Finsupp.update_apply, Finsupp.single_apply, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show i ≠ 3 by omega, show i ≠ 4 by omega, show i ≠ 5 by omega, show i ≠ 6 by omega, show i ≠ 7 by omega, show 0 ≠ i by omega, show 1 ≠ i by omega, show 2 ≠ i by omega, show 3 ≠ i by omega, show 4 ≠ i by omega, show 5 ≠ i by omega, show 6 ≠ i by omega, show 7 ≠ i by omega]
    · intro i
      by_cases hi : i<8
      · interval_cases i <;> simp [ReadNatProof.regs, Finsupp.update_apply, Finsupp.single_apply] <;> omega
      · simp [ReadNatProof.regs, Finsupp.update_apply, Finsupp.single_apply, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show i ≠ 3 by omega, show i ≠ 4 by omega, show i ≠ 5 by omega, show i ≠ 6 by omega, show i ≠ 7 by omega, show 0 ≠ i by omega, show 1 ≠ i by omega, show 2 ≠ i by omega, show 3 ≠ i by omega, show 4 ≠ i by omega, show 5 ≠ i by omega, show 6 ≠ i by omega, show 7 ≠ i by omega]

theorem run_then {α : Type*} (f : α → α) (Q : α → Prop) (a b : ℕ) (s t u : α)
    (ha : f^[a] s=t ∧ ∀ j ≤ a, Q (f^[j] s))
    (hb : f^[b] t=u ∧ ∀ j ≤ b, Q (f^[j] t)) :
    f^[a+b] s=u ∧ ∀ j ≤ a+b, Q (f^[j] s) := by
  constructor
  · rw [Nat.add_comm a b, Function.iterate_add_apply, ha.1, hb.1]
  · apply ReadNatProof.trace_append f Q s a b ha.2
    rw [ha.1]; exact hb.2

theorem code_run (inp : List Bool) (ω : ℕ → Bool) (R pos h w t : ℕ)
    (hR : 2 ≤ R) (hh : h ≤ R) (hw : w ≤ R) (ht : t ≤ R) (hu : 2^h ≤ R)
    (hL : wordLength h ≤ R) (hpows : ∀ i ≤ wordLength h, i^i ≤ R) :
    (shapeStep wordLengthCode inp ω)^[4*h+10+searchTicks 0 (wordLength h)]
      (ReadNatProof.state 0 pos h w 0 t) =
      state 22 pos h (2^h) (wordLength h) ((wordLength h)^(wordLength h)) (wordLength h) true ∧
    ∀ j ≤ 4*h+10+searchTicks 0 (wordLength h), Bounded R
      ((shapeStep wordLengthCode inp ω)^[j] (ReadNatProof.state 0 pos h w 0 t)) := by
  have hi := And.intro (initial_run inp ω pos h w t) (initial_trace inp ω R pos h w t hR hh hw ht)
  have he := exp_loop inp ω R pos h 0 1 0 h (by omega) hR hh hu (by omega) (by omega)
  simp only [pow_zero] at he
  have he' := run_then (shapeStep wordLengthCode inp ω) (Bounded R) 7 (4*h+2) _ _ _ hi he
  have hs : (shapeStep wordLengthCode inp ω)^[1] (state 12 pos h (2^h) 0 1 h) =
      state 13 pos h (2^h) 0 1 h ∧
      ∀ j ≤ 1, Bounded R ((shapeStep wordLengthCode inp ω)^[j] (state 12 pos h (2^h) 0 1 h)) := by
    constructor
    · simpa using step_12 inp ω pos h (2^h) 0 1 h
    · intro j hj; interval_cases j <;> simp only [Function.iterate_zero, id_eq, Function.iterate_one, step_12]
      all_goals apply bounded_state <;> omega
  have hs' := run_then (shapeStep wordLengthCode inp ω) (Bounded R) (7+(4*h+2)) 1 _ _ _ he' hs
  have hf := search_loop inp ω R pos h 0 (wordLength h) 1 h (by omega)
    hR hh hu hL (by omega) hh hpows
  have hall := run_then (shapeStep wordLengthCode inp ω) (Bounded R) ((7+(4*h+2))+1)
    (searchTicks 0 (wordLength h)) _ _ _ hs' hf
  rw [show 7+(4*h+2)+1=4*h+10 by omega] at hall
  exact hall

theorem relocated_shape (precode P : Program) (inp : List Bool) (ω : ℕ → Bool)
    (s : State) (k : ℕ) :
    (shapeStep (placeAfter precode P) inp ω)^[k] (relocateState precode.length s) =
      relocateState precode.length ((shapeStep P inp ω)^[k] s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    unfold shapeStep
    rw [relocate_step]
    rfl

@[simp] theorem bounded_relocate (R offset : ℕ) (s : State) :
    Bounded R (relocateState offset s) ↔ Bounded R s := Iff.rfl

noncomputable def totalTicks (h : ℕ) : ℕ := 7*h.size+6+(4*h+10+searchTicks 0 (wordLength h))

theorem totalTicks_bound (h : ℕ) : totalTicks h ≤ 50*(h+2)^2 := by
  have hL := wordLength_le h
  have hs : h.size ≤ h+2 := Nat.size_le.mpr (by
    exact (Nat.lt_two_pow_self (n := h)).trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
  have hLsq : (wordLength h)^2 ≤ (h+2)^2 := Nat.pow_le_pow_left hL 2
  unfold totalTicks searchTicks
  nlinarith

end ITPIRPreproc.MatchVec.WordRAM.ParameterProof


set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000

namespace ITPIRPreproc.MatchVec.WordRAM.ParameterReaderProof
open ReadNatProof

theorem flag_step (inp : List Bool) (ω : ℕ → Bool) (pos a w f t : ℕ) :
    shapeStep wordLengthProgram inp ω (state 3 pos a w f t) =
      state 4 (pos+1) a w (inputVal inp[pos]?) t := by
  simp [shapeStep, eraseCost, step, wordLengthProgram, placeAfter, readNatJump, readNatProgram, state]

theorem branch_zero (inp : List Bool) (ω : ℕ → Bool) (pos a w t : ℕ) :
    shapeStep wordLengthProgram inp ω (state 4 pos a w 0 t) = state 5 pos a w 0 t := by
  simp [shapeStep, eraseCost, step, wordLengthProgram, placeAfter, readNatJump, readNatProgram, state]

theorem branch_one (inp : List Bool) (ω : ℕ → Bool) (pos a w t : ℕ) :
    shapeStep wordLengthProgram inp ω (state 4 pos a w 1 t) = state 6 pos a w 1 t := by
  simp [shapeStep, eraseCost, step, wordLengthProgram, placeAfter, readNatJump, readNatProgram, state]

theorem exit_step (inp : List Bool) (ω : ℕ → Bool) (pos a w f t : ℕ) :
    shapeStep wordLengthProgram inp ω (state 5 pos a w f t) = state 11 pos a w f t := by
  simp [shapeStep, eraseCost, step, wordLengthProgram, placeAfter, readNatJump, readNatProgram, state]

theorem bit_step (inp : List Bool) (ω : ℕ → Bool) (pos a w f t : ℕ) :
    shapeStep wordLengthProgram inp ω (state 6 pos a w f t) =
      state 7 (pos+1) a w f (inputVal inp[pos]?) := by
  simp [shapeStep, eraseCost, step, wordLengthProgram, placeAfter, readNatJump, readNatProgram, state]

theorem mul_step (inp : List Bool) (ω : ℕ → Bool) (pos a w f t : ℕ) :
    shapeStep wordLengthProgram inp ω (state 7 pos a w f t) = state 8 pos a w f (t*w) := by
  simp [shapeStep, eraseCost, step, wordLengthProgram, placeAfter, readNatJump, readNatProgram, state]

theorem add_step (inp : List Bool) (ω : ℕ → Bool) (pos a w f t : ℕ) :
    shapeStep wordLengthProgram inp ω (state 8 pos a w f t) = state 9 pos (a+t) w f t := by
  simp [shapeStep, eraseCost, step, wordLengthProgram, placeAfter, readNatJump, readNatProgram, state]

theorem weight_step (inp : List Bool) (ω : ℕ → Bool) (pos a w f t : ℕ) :
    shapeStep wordLengthProgram inp ω (state 9 pos a w f t) = state 10 pos a (w+w) f t := by
  simp [shapeStep, eraseCost, step, wordLengthProgram, placeAfter, readNatJump, readNatProgram, state]

theorem back_step (inp : List Bool) (ω : ℕ → Bool) (pos a w f t : ℕ) :
    shapeStep wordLengthProgram inp ω (state 10 pos a w f t) = state 3 pos a w f t := by
  simp [shapeStep, eraseCost, step, wordLengthProgram, placeAfter, readNatJump, readNatProgram, state]

theorem body_run (inp : List Bool) (ω : ℕ → Bool) (pos a w f t : ℕ) (b : Bool)
    (h0 : inp[pos]? = some true) (h1 : inp[pos+1]? = some b) :
    (shapeStep wordLengthProgram inp ω)^[7] (state 3 pos a w f t) =
      state 3 (pos+2) (a+b.toNat*w) (w+w) 1 (b.toNat*w) := by
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
    flag_step, branch_one, bit_step, mul_step, add_step, weight_step, back_step,
    h0, h1, inputVal]
  cases b <;> rfl

theorem body_trace (inp : List Bool) (ω : ℕ → Bool) (R pos a w f t : ℕ) (b : Bool)
    (h0 : inp[pos]? = some true) (h1 : inp[pos+1]? = some b)
    (hR : 1 ≤ R) (ha : a < w) (hw : w+w ≤ R) (hf : f ≤ R) (ht : t ≤ R) :
    ∀ j ≤ 7, Bounded R ((shapeStep wordLengthProgram inp ω)^[j] (state 3 pos a w f t)) := by
  intro j hj
  interval_cases j <;>
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
      flag_step, branch_one, bit_step, mul_step, add_step, weight_step, back_step,
      h0, h1, inputVal]
  all_goals cases b <;> apply bounded_state <;> simp_all <;> omega

theorem stop_run (inp : List Bool) (ω : ℕ → Bool) (pos a w f t : ℕ)
    (h0 : inp[pos]? = some false) :
    (shapeStep wordLengthProgram inp ω)^[3] (state 3 pos a w f t) =
      state 11 (pos+1) a w 0 t := by
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
    flag_step, branch_zero, exit_step, h0, inputVal]

theorem stop_trace (inp : List Bool) (ω : ℕ → Bool) (R pos a w f t : ℕ)
    (h0 : inp[pos]? = some false) (hR : 1 ≤ R) (ha : a ≤ R)
    (hw : w ≤ R) (hf : f ≤ R) (ht : t ≤ R) :
    ∀ j ≤ 3, Bounded R ((shapeStep wordLengthProgram inp ω)^[j] (state 3 pos a w f t)) := by
  intro j hj
  interval_cases j <;>
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
      flag_step, branch_zero, exit_step, h0, inputVal]
  all_goals apply bounded_state <;> omega

theorem loop_run_and_trace (inp : List Bool) (ω : ℕ → Bool) (R : ℕ)
    (bs tail : List Bool) (pos a w f t : ℕ)
    (hinp : inp.drop pos = encBits bs ++ tail)
    (hwp : 0 < w) (ha : a < w) (hf : f ≤ 1) (ht : t ≤ w)
    (hcap : w * 2^bs.length ≤ R) :
    (∃ tf, (shapeStep wordLengthProgram inp ω)^[7*bs.length+3] (state 3 pos a w f t) =
      state 11 (pos+2*bs.length+1) (a+w*value bs) (w*2^bs.length) 0 tf) ∧
    (∀ j ≤ 7*bs.length+3,
      Bounded R ((shapeStep wordLengthProgram inp ω)^[j] (state 3 pos a w f t))) := by
  induction bs generalizing pos a w f t with
  | nil =>
    have h0 : inp[pos]? = some false := by
      have hx := congrArg (fun xs : List Bool => xs[0]?) hinp
      simpa [encBits] using hx
    have hwR : w ≤ R := by simpa using hcap
    constructor
    · refine ⟨t, ?_⟩
      simpa using stop_run inp ω pos a w f t h0
    · simpa using stop_trace inp ω R pos a w f t h0 (by omega) (by omega)
        hwR (by omega) (by omega)
  | cons b bs ih =>
    have h0 : inp[pos]? = some true := by
      have hx := congrArg (fun xs : List Bool => xs[0]?) hinp
      simpa [encBits] using hx
    have h1 : inp[pos+1]? = some b := by
      have hx := congrArg (fun xs : List Bool => xs[1]?) hinp
      simpa [encBits] using hx
    have hrest : inp.drop (pos+2) = encBits bs ++ tail := by
      have hx := congrArg (List.drop 2) hinp
      simpa [encBits, List.drop_drop, List.append_assoc, Nat.add_comm] using hx
    have hcap' : (w+w) * 2^bs.length ≤ R := by
      calc
        (w+w)*2^bs.length = w*2^(b::bs).length := by simp only [List.length_cons, pow_succ]; ring
        _ ≤ R := hcap
    have hwR : w+w ≤ R := by
      have hp : 0 < 2^bs.length := by positivity
      nlinarith only [hcap', hp]
    have ha' : a+b.toNat*w < w+w := by cases b <;> simp_all <;> omega
    have ht' : b.toNat*w ≤ w+w := by cases b <;> simp <;> omega
    obtain ⟨⟨tf, he⟩, hb⟩ := ih (pos+2) (a+b.toNat*w) (w+w) 1 (b.toNat*w)
      hrest (by omega) ha' le_rfl ht' hcap'
    have hbody := body_run inp ω pos a w f t b h0 h1
    constructor
    · refine ⟨tf, ?_⟩
      rw [List.length_cons,
        show 7*(bs.length+1)+3 = (7*bs.length+3)+7 by omega,
        Function.iterate_add_apply, hbody, he]
      congr 1
      · omega
      · rw [value_cons]
        ring
      · rw [pow_succ]
        ring
    · have hfirst := body_trace inp ω R pos a w f t b h0 h1
        (by omega) ha hwR (by omega) (by omega)
      have hlast : ∀ j ≤ 7*bs.length+3, Bounded R
          ((shapeStep wordLengthProgram inp ω)^[j]
            ((shapeStep wordLengthProgram inp ω)^[7] (state 3 pos a w f t))) := by
        rw [hbody]
        exact hb
      have hc := trace_append (shapeStep wordLengthProgram inp ω) (Bounded R)
        (state 3 pos a w f t) 7 (7*bs.length+3) hfirst hlast
      simpa [List.length_cons, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc

theorem initial_run (inp : List Bool) (ω : ℕ → Bool) :
    (shapeStep wordLengthProgram inp ω)^[3] initState = state 3 0 0 1 0 0 := by
  simp [Function.iterate_succ_apply', shapeStep, eraseCost, step, wordLengthProgram, placeAfter, readNatJump, readNatProgram,
    initState, state, regs]
  ext i
  simp [Finsupp.update_apply, Finsupp.single_apply]
  split_ifs <;> omega

theorem initial_trace (inp : List Bool) (ω : ℕ → Bool) (R : ℕ) (hR : 1 ≤ R) :
    ∀ j ≤ 3, Bounded R ((shapeStep wordLengthProgram inp ω)^[j] initState) := by
  intro j hj
  interval_cases j <;>
    simp [Function.iterate_succ_apply', shapeStep, eraseCost, step, wordLengthProgram, placeAfter, readNatJump, readNatProgram,
      initState, Bounded]
  all_goals simp [Finsupp.support_update, Finsupp.single_apply, Function.update_apply]
  all_goals try (refine ⟨by decide, ?_⟩)
  all_goals intro i; split_ifs <;> omega

theorem full_shape (n : ℕ) (tail : List Bool) (ω : ℕ → Bool) :
    (∃ tf, (shapeStep wordLengthProgram (encNat n ++ tail) ω)^[7*n.size+6] initState =
      state 11 (2*n.size+1) n (2^n.size) 0 tf) ∧
    (∀ j ≤ 7*n.size+6,
      Bounded (2^n.size) ((shapeStep wordLengthProgram (encNat n ++ tail) ω)^[j] initState)) := by
  have hinp : (encNat n ++ tail).drop 0 = encBits n.bits ++ tail := by rfl
  obtain ⟨⟨tf, he⟩, hb⟩ := loop_run_and_trace (encNat n ++ tail) ω (2^n.size)
    n.bits tail 0 0 1 0 0 hinp (by omega) (by omega) (by omega) (by omega)
    (by simp [Nat.size_eq_bits_len])
  have he' : (shapeStep wordLengthProgram (encNat n ++ tail) ω)^[7*n.size+3]
      (state 3 0 0 1 0 0) = state 11 (2*n.size+1) n (2^n.size) 0 tf := by
    simpa [Nat.size_eq_bits_len, value_bits] using he
  constructor
  · refine ⟨tf, ?_⟩
    rw [show 7*n.size+6 = (7*n.size+3)+3 by omega, Function.iterate_add_apply,
      initial_run, he']
  · have hfirst := initial_trace (encNat n ++ tail) ω (2^n.size)
        (by
          have hp : 0 < 2^n.size := by positivity
          omega)
    have hlast : ∀ j ≤ 7*n.size+3, Bounded (2^n.size)
        ((shapeStep wordLengthProgram (encNat n ++ tail) ω)^[j]
          ((shapeStep wordLengthProgram (encNat n ++ tail) ω)^[3] initState)) := by
      rw [initial_run]
      simpa [Nat.size_eq_bits_len] using hb
    have hc := trace_append (shapeStep wordLengthProgram (encNat n ++ tail) ω)
      (Bounded (2^n.size)) initState 3 (7*n.size+3) hfirst hlast
    simpa only [show 3+(7*n.size+3) = 7*n.size+6 by omega] using hc


end ITPIRPreproc.MatchVec.WordRAM.ParameterReaderProof


set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000

namespace ITPIRPreproc.MatchVec.WordRAM.ParameterProof
open PolynomialConstruction

theorem full_shape (h : ℕ) (tail : List Bool) (ω : ℕ → Bool) :
    (shapeStep wordLengthProgram (encNat h++tail) ω)^[totalTicks h] initState =
      relocateState 11 (state 22 (2*h.size+1) h (2^h) (wordLength h)
        ((wordLength h)^(wordLength h)) (wordLength h) true) ∧
    ∀ j ≤ totalTicks h, Bounded (valueCap h)
      ((shapeStep wordLengthProgram (encNat h++tail) ω)^[j] initState) := by
  obtain ⟨hR,hhR,hu,hw,hpows⟩ := cap_bounds h
  have hh : h ≤ valueCap h := by omega
  have hL : wordLength h ≤ valueCap h := (wordLength_le h).trans hhR
  obtain ⟨⟨tf,he⟩,ht⟩ := ParameterReaderProof.full_shape h tail ω
  have htf : tf ≤ valueCap h := by
    have hf := (ht (7*h.size+6) le_rfl).2.2.2 3
    rw [he] at hf
    have hsmall : tf ≤ 2^h.size := by simpa [ReadNatProof.state] using hf
    exact hsmall.trans hw
  have hc := code_run (encNat h++tail) ω (valueCap h) (2*h.size+1) h (2^h.size) tf
    hR hh hw htf hu hL hpows
  have hcode :
      (shapeStep wordLengthProgram (encNat h++tail) ω)^[4*h+10+searchTicks 0 (wordLength h)]
        (ReadNatProof.state 11 (2*h.size+1) h (2^h.size) 0 tf) =
        relocateState 11 (state 22 (2*h.size+1) h (2^h) (wordLength h)
          ((wordLength h)^(wordLength h)) (wordLength h) true) ∧
      ∀ j ≤ 4*h+10+searchTicks 0 (wordLength h), Bounded (valueCap h)
        ((shapeStep wordLengthProgram (encNat h++tail) ω)^[j]
          (ReadNatProof.state 11 (2*h.size+1) h (2^h.size) 0 tf)) := by
    have hl : (readNatJump 11).length=11 := by decide
    constructor
    · change (shapeStep (placeAfter (readNatJump 11) wordLengthCode) (encNat h++tail) ω)^[_]
        (relocateState (readNatJump 11).length (ReadNatProof.state 0 (2*h.size+1) h (2^h.size) 0 tf)) = _
      rw [relocated_shape, hc.1, hl]
    · intro j hj
      change Bounded (valueCap h)
        ((shapeStep (placeAfter (readNatJump 11) wordLengthCode) (encNat h++tail) ω)^[j]
          (relocateState (readNatJump 11).length (ReadNatProof.state 0 (2*h.size+1) h (2^h.size) 0 tf)))
      rw [relocated_shape, bounded_relocate]
      exact hc.2 j hj
  have hreader : ∀ j ≤ 7*h.size+6, Bounded (valueCap h)
      ((shapeStep wordLengthProgram (encNat h++tail) ω)^[j] initState) := by
    intro j hj
    obtain ⟨hm,ho,hs,hv⟩ := ht j hj
    exact ⟨hm,ho,hs.trans (Finset.range_mono (by omega)),fun i => (hv i).trans hw⟩
  exact run_then (shapeStep wordLengthProgram (encNat h++tail) ω) (Bounded (valueCap h))
    (7*h.size+6) (4*h+10+searchTicks 0 (wordLength h)) _ _ _ ⟨he,hreader⟩ hcode

theorem program_deterministic : Deterministic wordLengthProgram := by
  simp [Deterministic, wordLengthProgram, placeAfter, readNatJump, readNatProgram,
    wordLengthCode, relocateInstr]

theorem program_streaming : Streaming wordLengthProgram := by
  simp [Streaming, wordLengthProgram, placeAfter, readNatJump, readNatProgram,
    wordLengthCode, relocateInstr]

theorem program_correct (h : ℕ) (tail : List Bool) (ω : ℕ → Bool) :
    Halts wordLengthProgram (encNat h++tail) ω ∧
    (finalState wordLengthProgram (encNat h++tail) ω).regs 0=h ∧
    (finalState wordLengthProgram (encNat h++tail) ω).regs 1=2^h ∧
    (finalState wordLengthProgram (encNat h++tail) ω).regs 2=wordLength h ∧
    (finalState wordLengthProgram (encNat h++tail) ω).inPos=(encNat h).length ∧
    output wordLengthProgram (encNat h++tail) ω=[] ∧
    haltStep wordLengthProgram (encNat h++tail) ω ≤ 50*(h+2)^2 ∧
    cost wordLengthProgram (encNat h++tail) ω ≤ 200*(h+2)^4 ∧
    workingBits wordLengthProgram (encNat h++tail) ω ≤ 8*((h+2)^2+1) := by
  obtain ⟨he,ht⟩ := full_shape h tail ω
  have hs : eraseCost (run wordLengthProgram (encNat h++tail) ω (totalTicks h)) =
      relocateState 11 (state 22 (2*h.size+1) h (2^h) (wordLength h)
        ((wordLength h)^(wordLength h)) (wordLength h) true) := by
    rw [run_shape]; exact he
  have hh : (run wordLengthProgram (encNat h++tail) ω (totalTicks h)).halted=true :=
    congrArg State.halted hs
  have hfinal := finalState_eq_run _ _ _ _ hh
  have hbound (j : ℕ) (hj : j ≤ totalTicks h) :
      Bounded (valueCap h) (run wordLengthProgram (encNat h++tail) ω j) := by
    have hb := ht j hj
    rw [← run_shape] at hb
    exact hb
  have hbits (j : ℕ) (hj : j ≤ totalTicks h) (i : ℕ) :
      Nat.size ((run wordLengthProgram (encNat h++tail) ω j).regs i) ≤ bitCap h+1 := by
    have hb := Nat.size_le_size ((hbound j hj).2.2.2 i)
    simpa [valueCap, Nat.size_pow] using hb
  refine ⟨⟨totalTicks h,hh⟩,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hfinal]
    simpa [eraseCost, relocateState, state] using congrArg (fun s : State => s.regs 0) hs
  · rw [hfinal]
    simpa [eraseCost, relocateState, state] using congrArg (fun s : State => s.regs 1) hs
  · rw [hfinal]
    simpa [eraseCost, relocateState, state] using congrArg (fun s : State => s.regs 2) hs
  · rw [hfinal, ReadNatProof.encNat_length]
    exact congrArg State.inPos hs
  · rw [output_eq_run _ _ _ _ hh]
    exact congrArg State.out hs
  · exact (haltStep_le _ _ _ _ hh).trans (totalTicks_bound h)
  · rw [cost_eq_run _ _ _ _ hh]
    have hcap4 : 4 ≤ (h+2)^2 := Nat.pow_le_pow_left (show 2 ≤ h+2 by omega) 2
    have hc := cost_le_of_step_bound wordLengthProgram (encNat h++tail) ω
      (totalTicks h) (1+2*(bitCap h+1)) (by
        intro j hj
        apply step_cost_bound _ _ _ _ _ (hbits j (by omega))
        · intro i; rw [(hbound j (by omega)).1]; simp
        · intro d k hk
          have hk2 : k ≤ 2 := by
            simp [wordLengthProgram, placeAfter, readNatJump, readNatProgram,
              wordLengthCode, relocateInstr] at hk
            omega
          have hb := Nat.size_le_size hk2
          rw [show Nat.size 2=2 by decide] at hb
          unfold bitCap
          omega)
    have hp : 1+2*(bitCap h+1) ≤ 3*(h+2)^2 := by unfold bitCap; omega
    calc
      _ ≤ totalTicks h*(1+2*(bitCap h+1)) := hc
      _ ≤ (50*(h+2)^2)*(3*(h+2)^2) := Nat.mul_le_mul (totalTicks_bound h) hp
      _ ≤ 200*(h+2)^4 := by nlinarith [sq_nonneg ((h+2 : ℕ)^2)]
  · apply workingBits_le_of_trace _ _ _ (totalTicks h) _ hh
    intro j hj
    obtain ⟨hm,ho,hr,hv⟩ := hbound j hj
    exact space_le_of_registers _ 8 (bitCap h+1) hm ho hr (hbits j hj)

end ITPIRPreproc.MatchVec.WordRAM.ParameterProof

theorem solution :
    Deterministic wordLengthProgram ∧ Streaming wordLengthProgram ∧
    ∀ (h : ℕ) (tail : List Bool) (ω : ℕ → Bool),
    Halts wordLengthProgram (encNat h++tail) ω ∧
    (finalState wordLengthProgram (encNat h++tail) ω).regs 0=h ∧
    (finalState wordLengthProgram (encNat h++tail) ω).regs 1=2^h ∧
    (finalState wordLengthProgram (encNat h++tail) ω).regs 2=wordLength h ∧
    (finalState wordLengthProgram (encNat h++tail) ω).inPos=(encNat h).length ∧
    output wordLengthProgram (encNat h++tail) ω=[] ∧
    haltStep wordLengthProgram (encNat h++tail) ω ≤ 50*(h+2)^2 ∧
    cost wordLengthProgram (encNat h++tail) ω ≤ 200*(h+2)^4 ∧
    workingBits wordLengthProgram (encNat h++tail) ω ≤ 8*((h+2)^2+1) := by
  exact ⟨ParameterProof.program_deterministic, ParameterProof.program_streaming, ParameterProof.program_correct⟩
