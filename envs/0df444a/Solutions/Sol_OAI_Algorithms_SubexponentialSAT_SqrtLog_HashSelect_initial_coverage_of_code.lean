-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.initial_coverage_of_code
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:45:52.862032+00:00
-- url     : https://prove2.me/submissions/2ed653af-78cc-4172-9a12-4c0dd25eefd0

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S031
import Definitions.Def_OAIQ081S043

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashFamily
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashFamily

open scoped BigOperators
open Finset

theorem row_dot {m d : ℕ} (h : Candidate m d) (v : Fin m → ZMod 3) :
    (∑ i, row h i * v i) = eval h v := by
  simp only [row, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp [ite_mul ]

theorem candidate_card (m d : ℕ) :
    Fintype.card (Candidate m d) = (3 * m) ^ d := by
  simp [Candidate, IndexTuple, CoeffTuple, mul_pow, Nat.mul_comm]

private theorem coeffMap_surjective {m d : ℕ} (e : IndexTuple m d)
    (v : Fin m → ZMod 3) (hit : ∃ j, v (e j) ≠ 0) :
    Function.Surjective (coeffMap e v) := by
  obtain ⟨j, hj⟩ := hit
  intro a
  refine ⟨Pi.single j (a / v (e j)), ?_⟩
  simp [coeffMap, Pi.single_apply, hj]

theorem coeff_detection {m d : ℕ} (e : IndexTuple m d)
    (v : Fin m → ZMod 3) (hit : ∃ j, v (e j) ≠ 0) :
    3 * (univ.filter fun c : CoeffTuple d => eval (e, c) v ≠ 0).card =
      2 * Fintype.card (CoeffTuple d) := by
  classical
  let f := coeffMap e v
  have surj : Function.Surjective f := coeffMap_surjective e v hit
  have fiber (a : ZMod 3) :
      (univ.filter fun c => f c = a).card = (univ.filter fun c => f c = 0).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (surj a) (surj 0)
  have total : Fintype.card (CoeffTuple d) =
      3 * (univ.filter fun c => f c = 0).card := by
    calc
      _ = ∑ a : ZMod 3, (univ.filter fun c => f c = a).card := by
        simpa using (Finset.card_eq_sum_card_fiberwise
          (s := (univ : Finset (CoeffTuple d))) (t := (univ : Finset (ZMod 3)))
          (f := f) (by intro x hx; simp))
      _ = _ := by simp_rw [fiber]; simp
  have partition :
      (univ.filter fun c : CoeffTuple d => f c = 0).card +
        (univ.filter fun c : CoeffTuple d => f c ≠ 0).card =
          Fintype.card (CoeffTuple d) := by
    simpa using
      (Finset.card_filter_add_card_filter_not
        (s := (univ : Finset (CoeffTuple d))) (fun c => f c = 0))
  change 3 * (univ.filter fun c : CoeffTuple d => f c ≠ 0).card = _
  omega

private theorem pow_add_linear_lower (a b d : ℕ) :
    a ^ (d + 1) + (d + 1) * b * a ^ d ≤ (a + b) ^ (d + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h := Nat.mul_le_mul_right (a + b) ih
    simp only [pow_succ] at h ⊢
    nlinarith [Nat.zero_le (d * b * b * a ^ d), Nat.zero_le (b * b * a ^ d)]

theorem miss_power_le_half {m w d : ℕ} (hm : 0 < m) (hw : w ≤ m)
    (hd : m ≤ d * w) : 2 * (m - w) ^ d ≤ m ^ d := by
  obtain ⟨d, rfl⟩ : ∃ e, d = e + 1 := by
    have : d ≠ 0 := by intro h; simp [h] at hd; omega
    exact ⟨d - 1, by omega⟩
  have h := pow_add_linear_lower (m - w) w d
  rw [Nat.sub_add_cancel hw] at h
  have hmul := Nat.mul_le_mul_right ((m - w) ^ d) hd
  have hmul' := Nat.mul_le_mul_right ((m - w) ^ d) (Nat.sub_le m w)
  rw [pow_succ] at h ⊢
  nlinarith

theorem miss_card {m d : ℕ} (v : Fin m → ZMod 3) :
    (univ.filter fun e : IndexTuple m d => ∀ j, v (e j) = 0).card =
      (m - supportCard v) ^ d := by
  classical
  have hz : (univ.filter fun i => v i = 0).card = m - supportCard v := by
    have h : (univ.filter fun i => v i = 0).card + supportCard v = m := by
      simpa [supportCard] using
        (Finset.card_filter_add_card_filter_not
          (s := (univ : Finset (Fin m))) (fun i => v i = 0))
    omega
  have heq : (univ.filter fun e : IndexTuple m d => ∀ j, v (e j) = 0) =
      Fintype.piFinset (fun _ : Fin d => univ.filter fun i => v i = 0) := by
    ext e
    simp
  rw [heq, Fintype.card_piFinset_const, hz]

theorem hit_card_lower {m d : ℕ} (v : Fin m → ZMod 3) (hm : 0 < m)
    (heavy : m ≤ d * supportCard v) : m ^ d ≤ 2 * hitCard (d := d) v := by
  classical
  have hw : supportCard v ≤ m := by
    simpa [supportCard] using
      (Finset.card_filter_le (univ : Finset (Fin m)) (fun i => v i ≠ 0))
  have hp := miss_power_le_half hm hw heavy
  have partition := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (IndexTuple m d))) (fun e => ∃ j, v (e j) ≠ 0)
  simp only [not_exists, not_not] at partition
  rw [miss_card] at partition
  have hc : Fintype.card (IndexTuple m d) = m ^ d := by
    simp [IndexTuple ]
  simp only [Finset.card_univ, hc] at partition
  change hitCard v + (m - supportCard v) ^ d = m ^ d at partition
  omega

theorem detecting_card_sum {m d : ℕ} (v : Fin m → ZMod 3) :
    detectingCard (d := d) v =
      ∑ e : IndexTuple m d,
        (univ.filter fun c : CoeffTuple d => eval (e, c) v ≠ 0).card := by
  classical
  simp only [detectingCard, Finset.card_filter, Fintype.sum_prod_type]

theorem detecting_card_exact {m d : ℕ} (v : Fin m → ZMod 3) :
    3 * detectingCard (d := d) v =
      2 * Fintype.card (CoeffTuple d) * hitCard (d := d) v := by
  classical
  have per (e : IndexTuple m d) :
      3 * (univ.filter fun c : CoeffTuple d => eval (e, c) v ≠ 0).card =
        if ∃ j, v (e j) ≠ 0 then 2 * Fintype.card (CoeffTuple d) else 0 := by
    split_ifs with hit
    · exact coeff_detection e v hit
    · have hzero : ∀ j, v (e j) = 0 := by simpa using hit
      simp [eval, hzero]
  rw [detecting_card_sum, Finset.mul_sum]
  simp_rw [per]
  rw [← Finset.sum_filter]
  simp [hitCard, Nat.mul_comm]

/-- At least one third of the indexed sparse rows detect any vector whose
support times the tuple length is at least the ambient dimension. -/
theorem detecting_card_lower {m d : ℕ} (v : Fin m → ZMod 3) (hm : 0 < m)
    (heavy : m ≤ d * supportCard v) :
    Fintype.card (Candidate m d) ≤ 3 * detectingCard (d := d) v := by
  have h := Nat.mul_le_mul_right (Fintype.card (CoeffTuple d))
    (hit_card_lower v hm heavy)
  rw [detecting_card_exact]
  simpa [Candidate, IndexTuple, Fintype.card_fun, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using h

end SubexponentialSAT.SqrtLog.HashFamily

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashFamilyEnumeration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashFamily

open scoped BigOperators
open Finset

theorem enumerate_detecting_card {m d : ℕ} (v : Fin m → ZMod 3) :
    (univ.filter fun i : Fin ((3 * m) ^ d) => eval (enumerate m d i) v ≠ 0).card =
      detectingCard (d := d) v := by
  classical
  unfold detectingCard
  exact Finset.card_equiv (candidateEquivFin m d).symm (fun i => by
    constructor
    · intro hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simpa only [enumerate] using (Finset.mem_filter.mp hi).2
    · intro hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simpa only [enumerate] using (Finset.mem_filter.mp hi).2)

/-- The indexed family detects every heavy vector on at least a third of its
indices, with repetitions in coordinate tuples and even repeated rows kept. -/
theorem enumerate_detection {m d : ℕ} (v : Fin m → ZMod 3) (hm : 0 < m)
    (heavy : m ≤ d * supportCard v) :
    (3 * m) ^ d ≤
      3 * (univ.filter fun i : Fin ((3 * m) ^ d) =>
        (∑ j, row (enumerate m d i) j * v j) ≠ 0).card := by
  simp_rw [row_dot]
  rw [enumerate_detecting_card, ← candidate_card]
  exact detecting_card_lower v hm heavy

end SubexponentialSAT.SqrtLog.HashFamily

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual clause violations and sparse hash factors on the original variables. -/

namespace SubexponentialSAT.SqrtLog.HashInput


open scoped BigOperators
noncomputable section

variable {V E I R : Type*} [DecidableEq V] [CommRing R]

section Hash
variable [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
omit [DecidableEq V] in
theorem violationWeight_eq_zero_iff (C : E → SAT.Clause V) (x : SAT.Assignment V) :
    violationWeight C x = 0 ↔ ∀ e, (C e).eval x = true := by
  simp [violationWeight, Finset.sum_eq_zero_iff]

omit [Fintype E] [DecidableEq E] in
omit [DecidableEq V] in
theorem violationVector_eq_zero_iff [Nontrivial R] (C : E → SAT.Clause V)
    (x : SAT.Assignment V) :
    violationVector (R := R) C x = 0 ↔ ∀ e, (C e).eval x = true := by
  simp [funext_iff, violationVector, clauseValue]

end Hash
end
end SubexponentialSAT.SqrtLog.HashInput

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact natural-valued mass for finite sparse-hash selection.
The row semantics are abstract here; no evaluator is assumed computable
from this definition at the target cost. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

open scoped BigOperators

variable {X R I : Type*}

theorem survival_bound_of_detection [Fintype I]
    (rowAccept : R → X → Bool) (family : I → R) (x : X)
    (hdetect : Fintype.card I ≤
      3 * (Finset.univ.filter (fun i => rowAccept (family i) x = false)).card) :
    3 * survivingCandidates rowAccept family x ≤ 2 * Fintype.card I := by
  classical
  have hsurv : survivingCandidates rowAccept family x =
      (Finset.univ.filter (fun i => rowAccept (family i) x = true)).card := by
    simp [survivingCandidates]
  have hp := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset I)) (fun i => rowAccept (family i) x = true)
  have hf : (Finset.univ.filter (fun i => ¬ rowAccept (family i) x = true)) =
      Finset.univ.filter (fun i => rowAccept (family i) x = false) := by
    ext i
    cases h : rowAccept (family i) x <;> simp [h]
  rw [hf] at hp
  simp only [Finset.card_univ] at hp
  omega

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectTuple
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete indexed tuple family discharges the selector's coverage
hypothesis from a supplied lower-support code. All tuples, including repeated
coordinates and repeated resulting rows, remain in the enumeration. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

open scoped BigOperators

theorem tupleRows_survival {n m d : ℕ} (C : Fin m → SAT.Clause (Fin n))
    (x : SAT.Assignment (Fin n)) (hm : 0 < m)
    (heavy : m ≤ d * HashFamily.supportCard
      (HashInput.violationVector (R := ZMod 3) C x)) :
    3 * survivingCandidates (cnfRowAccept C) (tupleRows m d) x ≤
      2 * (3 * m) ^ d := by
  have hd := HashFamily.enumerate_detection
    (HashInput.violationVector (R := ZMod 3) C x) hm heavy
  have h : 3 * survivingCandidates (cnfRowAccept C) (tupleRows m d) x ≤
      2 * Fintype.card (Fin ((3 * m) ^ d)) := by
    apply survival_bound_of_detection (cnfRowAccept C) (tupleRows m d) x
    have hcard :
        ({i | cnfRowAccept C (tupleRows m d i) x = false} :
          Finset (Fin ((3 * m) ^ d))).card =
        ({i | ∑ e, HashFamily.row (HashFamily.enumerate m d i) e *
          HashInput.violationVector (R := ZMod 3) C x e ≠ 0} :
          Finset (Fin ((3 * m) ^ d))).card := by
      apply Finset.card_bij' (fun i _ => i) (fun i _ => i)
      · intro i hi
        have hbool := (Finset.mem_filter.mp hi).2
        have hne : ∑ e, HashFamily.row (HashFamily.enumerate m d i) e *
            HashInput.violationVector (R := ZMod 3) C x e ≠ 0 :=
          decide_eq_false_iff_not.mp hbool
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
      · intro i hi
        have hne := (Finset.mem_filter.mp hi).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact decide_eq_false_iff_not.mpr hne
      · intro i hi
        rfl
      · intro i hi
        rfl
    simpa only [Fintype.card_fin, hcard] using hd
  simpa using h

theorem tupleFamily_survival {n m d c : ℕ} (C : Fin m → SAT.Clause (Fin n))
    (hcount : (3 * m) ^ d = c + 1) (x : SAT.Assignment (Fin n)) (hm : 0 < m)
    (heavy : m ≤ d * HashFamily.supportCard
      (HashInput.violationVector (R := ZMod 3) C x)) :
    3 * survivingCandidates (cnfRowAccept C) (tupleFamily hcount) x ≤
      2 * (c + 1) := by
  have hs : survivingCandidates (cnfRowAccept C) (tupleFamily hcount) x =
      survivingCandidates (cnfRowAccept C) (tupleRows m d) x := by
    exact Fintype.sum_equiv (finCongr hcount.symm) _ _ (fun _ => rfl)
  rw [hs, ← hcount]
  exact tupleRows_survival C x hm heavy

theorem supportCard_eq_codeWeight {m : ℕ} (v : Fin m → ZMod 3) :
    HashFamily.supportCard v = SparseCode.weight v := rfl

theorem initial_coverage_of_code_oai {n m d c : ℕ}
    (C : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
    (hcount : (3 * m) ^ d = c + 1) (initial : List (Row m))
    (hcode : ∀ v : Row m,
      (∀ r ∈ initial, (∑ e, r e * v e) = 0) → v ≠ 0 →
      m ≤ d * SparseCode.weight v) :
    ∀ x, accepts (cnfRowAccept C) initial x = true →
      0 < HashInput.violationWeight C x →
      3 * survivingCandidates (cnfRowAccept C) (tupleFamily hcount) x ≤
        2 * (c + 1) := by
  intro x hx hw
  apply tupleFamily_survival C hcount x hm
  rw [supportCard_eq_codeWeight]
  apply hcode
  · intro r hr
    have ha := List.all_eq_true.mp hx r hr
    simpa [cnfRowAccept] using ha
  · intro hv
    have hs := (HashInput.violationVector_eq_zero_iff (R := ZMod 3) C x).mp hv
    have hz := (HashInput.violationWeight_eq_zero_iff C x).mpr hs
    omega

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.initial_coverage_of_code_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.initial_coverage_of_code_oai
