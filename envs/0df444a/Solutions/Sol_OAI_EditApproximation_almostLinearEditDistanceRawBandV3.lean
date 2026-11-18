-- Prove2me | solution 1 for OAI.EditApproximation.almostLinearEditDistanceRawBandV3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:43:04.055385+00:00
-- url     : https://prove2.me/submissions/134b45fb-4f20-44bf-9096-d4f170aec365

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_07
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_EditApproxScheme_17
import Definitions.Def_EditApproxScheme_18
import Definitions.Def_EditApproxScheme_20
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_integerBinaryAnswer_conditional_accuracy
import Theorems.Thm_OAI_EditApproximation_integerBinarySpaceFootprintRawBand_eq
import Theorems.Thm_OAI_EditApproximation_integerBinarySpaceFootprint_eq
import Theorems.Thm_OAI_EditApproximation_integerBinarySpace_polynomial
import Theorems.Thm_OAI_EditApproximation_integerBinaryWork_expected_near_linear

section
-- module Solutions.OAIQ361V3_EA.EditDistance_Metric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Unrestricted edit scripts, metric inequalities, and common subsequences
-/

namespace EditDistortion

universe u v

variable {Alpha : Type u} {Beta : Type v} {s : Bool}

namespace Script

theorem eq_of_zero {x y : List Alpha} (h : Script s 0 x y) : x = y := by
  cases h
  rfl

end Script



theorem cost_eq_zero_iff {x y : List Alpha} : cost s x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hc := cost_spec (s := s) x y
    rw [h] at hc
    exact hc.eq_of_zero
  · rintro rfl
    exact cost_refl _

end EditDistortion

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_ExactSuffixDP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! An exact suffix dynamic program for the bounded initial input range.
Each source row is computed once; its cells minimize over target cuts.
The singleton prefix cost is the executable occurrence formula. -/

namespace EditApproximation

open EditDistortion



theorem natListMinimum_le_member (fallback value : ℕ) (values : List ℕ) (h : value ∈ values) :
    natListMinimum fallback values ≤ value := by
  induction values with
  | nil => simp only [List.not_mem_nil] at h
  | cons first rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih h)

theorem natListMinimum_lower (fallback lower : ℕ) (values : List ℕ)
    (hfallback : lower ≤ fallback) (hvalues : ∀ value ∈ values, lower ≤ value) :
    lower ≤ natListMinimum fallback values := by
  induction values with
  | nil => exact hfallback
  | cons first rest ih =>
    exact le_min (hvalues first (List.mem_cons_self))
      (ih (fun value h => hvalues value (List.mem_cons_of_mem _ h)))



theorem ofFn_nat_getD {n j : ℕ} (f : Fin (n + 1) → ℕ) (hj : j ≤ n) :
    (List.ofFn f).getD j 0 = f ⟨j, Nat.lt_succ_of_le hj⟩ := by
  have hlt : j < (List.ofFn f).length := by simpa only [List.length_ofFn] using Nat.lt_succ_of_le hj
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]

theorem edit_nil_left_exact {α : Type*} (target : List α) : edit ([] : List α) target = target.length := by
  have hlo := (cost_length_bounds (s := true) ([] : List α) target).2
  have hup := edit_le_max_length ([] : List α) target
  simp only [List.length_nil, zero_add, max_eq_right (Nat.zero_le _)] at hlo hup
  exact Nat.le_antisymm hup hlo

theorem exactSuffixDP_spec {α : Type*} [DecidableEq α] (source target : List α) :
    ∀ j ≤ target.length, (exactSuffixDP source target).getD j 0 = edit source (target.drop j) := by
  induction source with
  | nil =>
    intro j hj
    rw [exactSuffixDP, ofFn_nat_getD _ hj, edit_nil_left_exact, List.length_drop]
  | cons a rest ih =>
    intro j hj
    rw [exactSuffixDP, ofFn_nat_getD _ hj]
    dsimp only
    have hcandidate (k : ℕ) (hk : k ≤ target.length - j) :
        edit (a :: rest) (target.drop j) ≤
          singletonCost a ((target.drop j).take k) + (exactSuffixDP rest target).getD (j + k) 0 := by
      rw [singletonCost_eq_edit, ih (j + k) (by omega)]
      have h := cost_append_le (s := true) [a] ((target.drop j).take k) rest ((target.drop j).drop k)
      rw [List.take_append_drop] at h
      simpa only [cost, edit, List.singleton_append, List.drop_drop] using h
    apply Nat.le_antisymm
    · obtain ⟨left, right, hsplit, hcost⟩ := edit_append_split [a] rest (target.drop j)
      have hk : left.length ≤ target.length - j := by
        have hlen := congrArg List.length hsplit
        simp only [List.length_drop, List.length_append] at hlen
        omega
      have hleft : (target.drop j).take left.length = left := by
        rw [hsplit]
        simp only [List.take_left]
      have hright : target.drop (j + left.length) = right := by
        rw [← List.drop_drop, hsplit]
        simp only [List.drop_left]
      have hm := natListMinimum_le_member
        (singletonCost a [] + (exactSuffixDP rest target).getD j 0)
        (singletonCost a ((target.drop j).take left.length) +
          (exactSuffixDP rest target).getD (j + left.length) 0)
        ((List.range (target.length - j + 1)).map fun k =>
          singletonCost a ((target.drop j).take k) + (exactSuffixDP rest target).getD (j + k) 0)
        (List.mem_map.mpr ⟨left.length, List.mem_range.mpr (by omega), rfl⟩)
      have hvalue : singletonCost a ((target.drop j).take left.length) +
          (exactSuffixDP rest target).getD (j + left.length) 0 = edit [a] left + edit rest right := by
        rw [hleft, singletonCost_eq_edit, ih (j + left.length) (by omega), hright]
      simpa only [List.singleton_append] using hm.trans_eq (hvalue.trans hcost.symm)
    · apply natListMinimum_lower
      · simpa only [List.take_zero, Nat.add_zero] using hcandidate 0 (Nat.zero_le _)
      · intro value hvalue
        rcases List.mem_map.mp hvalue with ⟨k, hk, rfl⟩
        exact hcandidate k (by have := List.mem_range.mp hk; omega)



theorem exactSuffixAnswer_eq_edit {α : Type*} [DecidableEq α] (source target : List α) :
    exactSuffixAnswer source target = edit source target := by
  simpa only [exactSuffixAnswer, List.drop_zero] using exactSuffixDP_spec source target 0 (Nat.zero_le _)

theorem exactSuffixAnswer_equal {α : Type*} [DecidableEq α] (source target : List α)
    (heq : source = target) : exactSuffixAnswer source target = 0 := by
  rw [exactSuffixAnswer_eq_edit]
  exact (cost_eq_zero_iff (s := true)).mpr heq

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerBinaryAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open MeasureTheory

theorem integerBinaryAnswer_equal (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction)
    (heq : source = target)
    (outcome : ComputedFullOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
    integerBinaryAnswer source target N epsilon outcome = 0 := by
  have hm : source.map integerSymbolCode = target.map integerSymbolCode := congrArg _ heq
  unfold integerBinaryAnswer
  split_ifs
  · cases outcome with
    | inl unitValue => exact exactSuffixAnswer_equal _ _ hm
    | inr execution =>
      simp only [integerBinaryOutput, computedQueryAnswerWithWork, hm, ite_true, if_true]
      rfl
  · exact exactSuffixAnswer_equal _ _ hm

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_AlmostLinearConditional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An edit-distance approximation scheme conditional on finite scalar
Bernstein concentration (Tropp, ACM217, corrected 2023, Theorem 4.16).
The same uniform binary algorithm is used in all four clauses. -/

namespace EditApproximation
open MeasureTheory Filter

/-- For each fixed binary accuracy in `(0,1)`, the concrete uniform algorithm
has success probability at least `2/3`, deterministic zero on equal inputs,
worst-case expected almost-linear time including preprocessing and sampling,
and polynomial space on every outcome. Alphabet bounds are analysis parameters,
not inputs to the algorithm. The finite initial range uses exact suffix DP. -/
theorem almostLinearEditDistance_conditional (epsilon : BinaryFraction)
    (hepsilon : 0 < epsilon.value) (_hepsilonOne : epsilon.value < 1)
    (bernstein : ∀ N, ComputedBernsteinInputs N) :
    (∀ (source target : List ℤ) (N : ℕ), source.length + target.length ≤ N →
      (2 / 3 : ℝ) ≤ (computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon).real
        {outcome | EditDistortion.edit source target ≤ integerBinaryAnswer source target N epsilon outcome ∧
          (integerBinaryAnswer source target N epsilon outcome : ℝ) ≤
            (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target}) ∧
    (∀ (source target : List ℤ) (N : ℕ), source = target → ∀ outcome,
      integerBinaryAnswer source target N epsilon outcome = 0) ∧
    (∀ (C : ℕ) (eta : ℝ), 0 < eta → ∀ᶠ N : ℕ in atTop,
      ∀ source target : List ℤ, source.length + target.length ≤ N →
        (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
        (∫ outcome, integerBinaryWork source target N epsilon outcome
          ∂computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon) ≤
            (N + 2 : ℝ) ^ (1 + eta)) ∧
    (∀ C : ℕ, ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ,
      source.length + target.length ≤ N →
        (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
        ∀ outcome, integerBinarySpace source target N epsilon outcome ≤ (N + 2) ^ (C + 65564)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro source target N hsize
    exact integerBinaryAnswer_conditional_accuracy source target N epsilon hepsilon hsize (bernstein N)
  · intro source target N heq outcome
    exact integerBinaryAnswer_equal source target N epsilon heq outcome
  · intro C eta heta
    exact integerBinaryWork_expected_near_linear C epsilon hepsilon eta heta
  · intro C
    exact integerBinarySpace_polynomial C epsilon hepsilon

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_BernsteinEnvelope
attribute [-instance] _root_.OAI.EditApproximation.physicalFamilyRange_neZero
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar exponential estimate used to discharge the finite Bernstein
input. Its rational majorant is proved by a derivative comparison, avoiding
any assumption of a concentration theorem. -/

namespace EditApproximation

private theorem bernsteinEnvelope_deriv (x : ℝ) (hx : x < 3) :
    HasDerivAt bernsteinEnvelope (Real.exp (-x) * (2 * x ^ 3 / (6 - 2 * x) ^ 2)) x := by
  have hd : (6 : ℝ) - 2 * x ≠ 0 := by linarith
  have hn := (((hasDerivAt_pow 2 x).add ((hasDerivAt_id x).const_mul 4)).add_const 6)
  have hb := (hasDerivAt_const x (6 : ℝ)).sub ((hasDerivAt_id x).const_mul 2)
  have h := ((hasDerivAt_id x).neg.exp).mul (hn.div hb hd)
  dsimp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] at h
  unfold bernsteinEnvelope
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  field_simp [hd]
  ring

private theorem bernsteinEnvelope_zero : bernsteinEnvelope 0 = 1 := by
  norm_num [bernsteinEnvelope]

theorem bernsteinEnvelope_one_le (x : ℝ) (hx : x < 3) : 1 ≤ bernsteinEnvelope x := by
  by_cases hpos : 0 ≤ x
  · have hc : ContinuousOn bernsteinEnvelope (Set.Icc 0 x) := by
      intro y hy
      exact (bernsteinEnvelope_deriv y (hy.2.trans_lt hx)).continuousAt.continuousWithinAt
    have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x) hc
      (fun y hy => (bernsteinEnvelope_deriv y ((interior_subset hy).2.trans_lt hx)).hasDerivWithinAt)
      (fun y hy => mul_nonneg (Real.exp_nonneg _) (div_nonneg
        (mul_nonneg (by norm_num) (pow_nonneg (interior_subset hy).1 3)) (sq_nonneg _)))
    simpa only [bernsteinEnvelope_zero] using hm ⟨le_rfl, hpos⟩ ⟨hpos, le_rfl⟩ hpos
  · have hneg : x ≤ 0 := le_of_not_ge hpos
    have hc : ContinuousOn bernsteinEnvelope (Set.Icc x 0) := by
      intro y hy
      exact (bernsteinEnvelope_deriv y (by linarith [hy.2])).continuousAt.continuousWithinAt
    have hm := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x 0) hc
      (fun y hy => (bernsteinEnvelope_deriv y (by linarith [(interior_subset hy).2])).hasDerivWithinAt)
      (fun y hy => mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) (div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (show y ^ 3 ≤ 0 by
          have h := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg y) (interior_subset hy).2
          nlinarith only [h]))
        (sq_nonneg _)))
    simpa only [bernsteinEnvelope_zero] using hm ⟨le_rfl, hneg⟩ ⟨hneg, le_rfl⟩ hneg

/-- Exact Bernstein exponential majorant, valid for all `x < 3`. -/
theorem exp_le_bernstein_envelope (x : ℝ) (hx : x < 3) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - x / 3)) := by
  have h := mul_le_mul_of_nonneg_left (bernsteinEnvelope_one_le x hx) (Real.exp_nonneg x)
  have hd : (6 : ℝ) - 2 * x ≠ 0 := by linarith
  have he : (2 : ℝ) * (1 - x / 3) ≠ 0 := by linarith
  have hc : (x ^ 2 + 4 * x + 6) / (6 - 2 * x) = 1 + x + x ^ 2 / (2 * (1 - x / 3)) := by
    have h3 : (3 : ℝ) - x ≠ 0 := by linarith
    field_simp [hd, he, h3]
    field_simp [show (6 : ℝ) - x * 2 ≠ 0 by linarith]
    ring
  simpa only [bernsteinEnvelope, mul_one, ← mul_assoc, ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, one_mul, hc] using h

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_BernsteinMGF
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalFamilyRange_neZero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalNodeFintype _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalScalarIndexFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open MeasureTheory ProbabilityTheory
open scoped BigOperators

section MGF
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem bounded_square_integrable (X : Ω → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hm : Measurable X) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b) :
    Integrable (fun ω => (X ω) ^ 2) μ := by
  apply Integrable.of_mem_Icc 0 (b ^ 2) (hm.pow_const 2).aemeasurable
  filter_upwards [hbound] with ω hω
  refine ⟨sq_nonneg _, ?_⟩
  have h := mul_le_mul hω hω (abs_nonneg _) hb
  simpa only [← pow_two, sq_abs] using h

theorem bounded_centered_mgf (X : Ω → ℝ) (b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t)
    (htb : t * b < 3) (hm : Measurable X) (hi : Integrable X μ)
    (hmean : (∫ ω, X ω ∂μ) = 0) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b) :
    mgf X μ t ≤ Real.exp ((t ^ 2 / (2 * (1 - t * b / 3))) * ∫ ω, (X ω) ^ 2 ∂μ) := by
  let c := t ^ 2 / (2 * (1 - t * b / 3))
  have hd : 0 < 2 * (1 - t * b / 3) := by linarith
  have hi2 := bounded_square_integrable μ X b hb.le hm hbound
  have hexp := integrable_exp_mul_of_le t b ht hm.aemeasurable
    (hbound.mono fun ω hω => (le_abs_self _).trans hω)
  have hpoint : ∀ᵐ ω ∂μ, Real.exp (t * X ω) ≤ 1 + t * X ω + c * (X ω) ^ 2 := by
    filter_upwards [hbound] with ω hω
    have hu : t * X ω ≤ t * b := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hω) ht
    have hx := exp_le_bernstein_envelope (t * X ω) (hu.trans_lt htb)
    have hdiv : (t * X ω) ^ 2 / (2 * (1 - t * X ω / 3)) ≤
        (t * X ω) ^ 2 / (2 * (1 - t * b / 3)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) hd
      linarith
    calc
      _ ≤ 1 + t * X ω + (t * X ω) ^ 2 / (2 * (1 - t * X ω / 3)) := hx
      _ ≤ 1 + t * X ω + (t * X ω) ^ 2 / (2 * (1 - t * b / 3)) := add_le_add le_rfl hdiv
      _ = _ := by dsimp only [c] <;> ring
  have h1 : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
  have hit := hi.const_mul t
  have hic := hi2.const_mul c
  have hineq := integral_mono_ae hexp ((h1.add hit).add hic) hpoint
  simp only [Pi.add_apply] at hineq
  have hadd := integral_add (h1.add hit) hic
  have hadd' := integral_add h1 hit
  simp only [Pi.add_apply] at hadd hadd'
  rw [hadd, hadd', integral_const_mul, integral_const_mul, hmean] at hineq
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero] at hineq
  exact hineq.trans (by simpa only [add_comm] using Real.add_one_le_exp (c * ∫ ω, (X ω) ^ 2 ∂μ))

theorem bounded_centered_sum_mgf {n : ℕ} (X : Fin n → Ω → ℝ)
    (b v t : ℝ) (hb : 0 < b) (ht : 0 ≤ t) (htb : t * b < 3)
    (hind : iIndepFun X μ) (hm : ∀ i, Measurable (X i))
    (hi : ∀ i, Integrable (X i) μ) (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (hvar : (∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) ≤ v) :
    mgf (fun ω => ∑ i, X i ω) μ t ≤ Real.exp (t ^ 2 * v / (2 * (1 - t * b / 3))) := by
  have hmgf := hind.mgf_sum hm Finset.univ (t := t)
  have hsum : (∑ i, X i) = fun ω => ∑ i, X i ω := by
    ext ω
    simp only [Finset.sum_apply]
  rw [hsum] at hmgf
  rw [hmgf]
  let c := t ^ 2 / (2 * (1 - t * b / 3))
  have hc : 0 ≤ c := div_nonneg (sq_nonneg _) (by linarith)
  calc
    _ ≤ ∏ i, Real.exp (c * ∫ ω, (X i ω) ^ 2 ∂μ) :=
      Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ =>
        bounded_centered_mgf μ (X i) b t hb ht htb (hm i) (hi i) (hmean i) (hbound i))
    _ = Real.exp (c * ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) := by
      rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ Real.exp (c * v) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hvar hc)
    _ = _ := by congr 1; dsimp only [c] <;> ring

end MGF
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_BernsteinFinite
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalFamilyRange_neZero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalNodeFintype _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalScalarIndexFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite scalar Bernstein concentration for independent
centered bounded real sums with a summed second-moment upper bound. -/

namespace EditApproximation
open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem bernstein_chernoff_exponent (b v d : ℝ) (hb : 0 < b)
    (hv : 0 < v) (hd : 0 < d) :
    let t := d / (v + b * d / 3);
    -t * d + t ^ 2 * v / (2 * (1 - t * b / 3)) =
      -d ^ 2 / (2 * v + (2 / 3 : ℝ) * b * d) := by
  let D := v + b * d / 3
  have hD : D ≠ 0 := ne_of_gt (by dsimp only [D] <;> positivity)
  have hunit : 1 - (d / D) * b / 3 = v / D := by
    field_simp [hD]
    dsimp only [D]
    ring
  change -(d / D) * d + (d / D) ^ 2 * v / (2 * (1 - (d / D) * b / 3)) = _
  rw [hunit]
  have hfinal : 2 * v + (2 / 3 : ℝ) * b * d = 2 * D := by dsimp only [D] <;> ring
  rw [hfinal]
  field_simp [hD, hv.ne']
  ring

theorem finite_bernstein_upper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (X : Fin n → Ω → ℝ) (b v d : ℝ)
    (hb : 0 < b) (hv : 0 < v) (hd : 0 < d)
    (hind : iIndepFun X μ) (hm : ∀ i, Measurable (X i))
    (hi : ∀ i, Integrable (X i) μ) (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (hvar : (∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) ≤ v) :
    μ.real {ω | d ≤ ∑ i, X i ω} ≤
      Real.exp (-d ^ 2 / (2 * v + (2 / 3 : ℝ) * b * d)) := by
  let t := d / (v + b * d / 3)
  have hden : 0 < v + b * d / 3 := by positivity
  have ht : 0 ≤ t := (div_pos hd hden).le
  have htb : t * b < 3 := by
    dsimp only [t]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith only [hv]
  have heach (i : Fin n) : Integrable (fun ω => Real.exp (t * X i ω)) μ :=
    integrable_exp_mul_of_le t b ht (hm i).aemeasurable
      ((hbound i).mono fun ω hω => (le_abs_self _).trans hω)
  have hsum : (∑ i, X i) = fun ω => ∑ i, X i ω := by
    ext ω
    simp only [Finset.sum_apply]
  have hsumint := hind.integrable_exp_mul_sum hm (s := Finset.univ) (fun i _ => heach i)
  rw [hsum] at hsumint
  have htail := measure_ge_le_exp_mul_mgf (μ := μ) (X := fun ω => ∑ i, X i ω) d ht hsumint
  have hmgf := bounded_centered_sum_mgf μ X b v t hb ht htb hind hm hi hmean hbound hvar
  calc
    _ ≤ Real.exp (-t * d) * mgf (fun ω => ∑ i, X i ω) μ t := htail
    _ ≤ Real.exp (-t * d) * Real.exp (t ^ 2 * v / (2 * (1 - t * b / 3))) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      exact bernstein_chernoff_exponent b v d hb hv hd

/-- Two-sided Bernstein concentration for independent centered bounded sums. -/
theorem finiteBernsteinInput {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : FiniteBernsteinInput μ := by
  intro n X b v d hb hv hd hind hm hi hmean hbound hvar
  have hplus := finite_bernstein_upper μ X b v d hb hv hd hind hm hi hmean hbound hvar
  have hnegind : iIndepFun (fun i ω => -X i ω) μ :=
    hind.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hnegmean (i) : (∫ ω, -X i ω ∂μ) = 0 := by rw [integral_neg, hmean, neg_zero]
  have hnegvar : (∑ i, ∫ ω, (-X i ω) ^ 2 ∂μ) ≤ v := by simpa only [neg_sq] using hvar
  have hminus := finite_bernstein_upper μ (fun i ω => -X i ω) b v d hb hv hd hnegind
    (fun i => (hm i).neg) (fun i => (hi i).neg) hnegmean
    (fun i => (hbound i).mono fun ω hω => by simpa only [abs_neg] using hω) hnegvar
  have hevent : {ω | d ≤ |∑ i, X i ω|} =
      {ω | d ≤ ∑ i, X i ω} ∪ {ω | d ≤ ∑ i, -X i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Finset.sum_neg_distrib]
    rw [le_abs]
  rw [hevent]
  exact (measureReal_union_le _ _).trans (by linarith only [hplus, hminus])

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_AlmostLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform binary approximation scheme for edit distance.
The finite Bernstein inequality supplies the concentration bounds for the
initial estimator and the refinement samples. -/

namespace EditApproximation
open MeasureTheory Filter

/-- Finite product-measure concentration for the initial estimator and refinement. -/
theorem computedBernsteinInputs (N : ℕ) : ComputedBernsteinInputs N := by
  constructor
  · exact finiteBernsteinInput _
  · intro b h
    exact finiteBernsteinInput _

/-- A uniform almost-linear approximation scheme. The same binary algorithm
satisfies the approximation, equality, expected-work and space bounds. -/
theorem almostLinearEditDistance (epsilon : BinaryFraction)
    (hepsilon : 0 < epsilon.value) (_hepsilonOne : epsilon.value < 1)
    :
    (∀ (source target : List ℤ) (N : ℕ), source.length + target.length ≤ N →
      (2 / 3 : ℝ) ≤ (computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon).real
        {outcome | EditDistortion.edit source target ≤ integerBinaryAnswer source target N epsilon outcome ∧
          (integerBinaryAnswer source target N epsilon outcome : ℝ) ≤
            (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target}) ∧
    (∀ (source target : List ℤ) (N : ℕ), source = target → ∀ outcome,
      integerBinaryAnswer source target N epsilon outcome = 0) ∧
    (∀ (C : ℕ) (eta : ℝ), 0 < eta → ∀ᶠ N : ℕ in atTop,
      ∀ source target : List ℤ, source.length + target.length ≤ N →
        (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
        (∫ outcome, integerBinaryWork source target N epsilon outcome
          ∂computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon) ≤
            (N + 2 : ℝ) ^ (1 + eta)) ∧
    (∀ C : ℕ, ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ,
      source.length + target.length ≤ N →
        (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
        ∀ outcome, integerBinarySpace source target N epsilon outcome ≤ (N + 2) ^ (C + 65564)) := by
  exact almostLinearEditDistance_conditional epsilon hepsilon _hepsilonOne computedBernsteinInputs

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_FootprintMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.EditApproximation
open Filter MeasureTheory
attribute [local instance] queryRoundsNeZero

theorem almostLinearEditDistance_main (epsilon : BinaryFraction)
    (hepsilon : 0 < epsilon.value) (_hepsilonOne : epsilon.value < 1)
    :
    (∀ (source target : List ℤ) (N : ℕ), source.length + target.length ≤ N →
      (2 / 3 : ℝ) ≤ (computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon).real
        {outcome | EditDistortion.edit source target ≤ integerBinaryAnswer source target N epsilon outcome ∧
          (integerBinaryAnswer source target N epsilon outcome : ℝ) ≤
            (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target}) ∧
    (∀ (source target : List ℤ) (N : ℕ), source = target → ∀ outcome,
      integerBinaryAnswer source target N epsilon outcome = 0) ∧
    (∀ (C : ℕ) (eta : ℝ), 0 < eta → ∀ᶠ N : ℕ in atTop,
      ∀ source target : List ℤ, source.length + target.length ≤ N →
        (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
        (∫ outcome, integerBinaryWork source target N epsilon outcome
          ∂computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon) ≤
            (N + 2 : ℝ) ^ (1 + eta)) ∧
    (∀ C : ℕ, ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ,
      source.length + target.length ≤ N →
        (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
        ∀ outcome, integerBinarySpaceFootprint source target N epsilon outcome ≤ (N + 2) ^ (C + 65564)) := by
  simpa only [integerBinarySpaceFootprint_eq] using
    almostLinearEditDistance epsilon hepsilon _hepsilonOne

end OAI.EditApproximation
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_RawBand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI.EditApproximation

namespace BinaryFraction



theorem preparedUnskippedReadWithWorkRaw_eq {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau F : BinaryFraction)
    (read initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R C : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
    (center : TargetInterval target.length) :
    preparedUnskippedReadWithWorkRaw parent b P exponent tau F read initial center =
      Prod.map (Option.map UnskippedBand.raw) id
        (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau F
          read initial R C hr hi center) := by
  have hbandValue : (preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo)
      b P tau (inversePowerTwo exponent) read).1 =
      representativeBandActions source target parent center b P tau.value
        ((2 : ℚ) ^ (-(exponent : ℤ))) (fun i q => (read i q).1.value) := by
    apply (preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
      b P tau (inversePowerTwo exponent) read R hr).1.trans
    simpa only [inversePowerTwo_value] using preparedRepresentativeWithWork_value source target
      parent center b P hP tau (inversePowerTwo exponent) (fun i q => (read i q).1)
  unfold preparedUnskippedReadWithWorkRaw preparedUnskippedReadWithWork
  dsimp only
  split_ifs with hempty hguard
  · rfl
  · simp only [Prod.map, Option.map_some, id_eq, UnskippedBand.raw, UnskippedBand.actions]
    congr 3
  · rfl

end BinaryFraction
end OAI.EditApproximation
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_RawBandBridges
attribute [-simp] _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.EditApproximation

theorem filterMapWithWork_map_raw {α β γ : Type*} (f : α → Option β × ℕ)
    (g : β → γ) (xs : List α) :
    filterMapWithWork (fun x => Prod.map (Option.map g) id (f x)) xs =
      Prod.map (List.map g) id (filterMapWithWork f xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [Prod.map, id_eq] at ih
    simp only [filterMapWithWork, Prod.map, id_eq, ih]
    cases (f x).1 <;> rfl

namespace BinaryFraction

theorem scoredArgmaxWithWork_map_raw {α β : Type*} (mapping : α → β)
    (score : β → BinaryFraction × ℕ) (values : List α) :
    scoredArgmaxWithWork score (values.map mapping) =
      Prod.map (Option.map (fun result => (mapping result.1, result.2))) id
        (scoredArgmaxWithWork (fun a => score (mapping a)) values) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, scoredArgmaxWithWork, ih, Prod.map, id_eq]
    cases (scoredArgmaxWithWork (fun a => score (mapping a)) tail).1 with
    | none => rfl
    | some best =>
      simp only [Option.map_some]
      split_ifs <;> rfl

theorem selectGroupWithWork_map_raw {α β : Type*} (mapping : α → β)
    (score : β → BinaryFraction × ℕ) (values : List α) (hne : values ≠ []) :
    selectGroupWithWork (values.map mapping) (by simpa using hne) score =
      Prod.map mapping id (selectGroupWithWork values hne (fun a => score (mapping a))) := by
  unfold selectGroupWithWork
  rw [scoredArgmaxWithWork_map_raw]
  simp only [Prod.map, id_eq, Option.map_map, Function.comp_def]
  cases values with
  | nil => exact False.elim (hne rfl)
  | cons head tail =>
    simp only [List.map_cons, List.head_cons]
    cases (scoredArgmaxWithWork (fun a => ((score (mapping a)).1.neg, (score (mapping a)).2 + 1))
      (head :: tail)).1 <;> rfl

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction) (child : Fin M → TargetInterval target.length → BinaryFraction)
  (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (initialAllocation currentAllocation : Fin M → TargetInterval target.length → ℕ)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)
  (drawSource : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M × ℕ)
  (drawAllocation : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → ℕ)

local notation "Member" => UnskippedBand source target parent b P exponent (value tau) (value F)
  (fun i q => value (child i q)) (fun i q => value (Prod.fst (initial i q)))

theorem chooseUnskippedSourceWithWorkRaw_eq (members : List Member) (hne : members ≠ []) :
    chooseUnskippedSourceWithWorkRaw b exponent Q initial current scales drawSource
      (members.map UnskippedBand.raw) (by simpa using hne) =
      Prod.map UnskippedBand.raw id
        (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F child initial current
          scales drawSource members hne) := by
  exact selectGroupWithWork_map_raw UnskippedBand.raw _ members hne

theorem sampledGroupActionSourceWithWorkRaw_eq (members : List Member) (hne : members ≠ []) :
    sampledGroupActionSourceWithWorkRaw b exponent Q initial current scales drawSource
      (members.map UnskippedBand.raw) (by simpa using hne) =
      sampledGroupActionSourceWithWork source target parent b P exponent Q tau F child initial current
        scales drawSource members hne := by
  let finish := fun selected : RawUnskippedBand M target.length × ℕ =>
    let rounded := roundedBandReadWithWork exponent b selected.1.actions selected.1.nonempty initial
    let result := endpointActionWithWork selected.1.center rounded.1.get
    (result.1, selected.2 + rounded.2 + result.2 + 3)
  exact congrArg finish (chooseUnskippedSourceWithWorkRaw_eq source target parent b P exponent Q
    tau F child initial current scales drawSource members hne)

end Group
end BinaryFraction
end OAI.EditApproximation
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_RawBandOuterBridges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.EditApproximation.BinaryFraction

theorem preparedOnlineReadWithWorkRaw_eq : @preparedOnlineReadWithWorkRaw = @preparedOnlineReadWithWork := by
  funext α source target M parent P F exponent H b hb hP tau eta kappa child initial table R hc hi t center integer
  unfold preparedOnlineReadWithWorkRaw preparedOnlineReadWithWork
  rw [preparedUnskippedReadWithWorkRaw_eq source target parent b P exponent hb hP tau (nat F)
    child initial R R hc hi center]
  simp only [Prod.map, id_eq, Option.isSome_map]

theorem preparedCellGroupSourceWithWorkRaw_eq : @preparedCellGroupSourceWithWorkRaw = @preparedCellGroupSourceWithWork := by
  funext α source target M parent b P F exponent Q hb hP tau a parentInitial child initial current
    R C hr hi raw hraw draw cell
  have hreader := funext (preparedUnskippedReadWithWorkRaw_eq source target parent b P exponent hb hP tau (nat F)
    child initial R C hr hi)
  let centers := (cellCentersReadWithWork P F b a (inversePowerTwo exponent) parentInitial cell).1
  have hmembers : filterMapWithWork
      (preparedUnskippedReadWithWorkRaw parent b P exponent tau (nat F) child initial) centers =
      Prod.map (List.map UnskippedBand.raw) id (filterMapWithWork
        (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
          child initial R C hr hi) centers) := by
    rw [hreader]
    exact filterMapWithWork_map_raw _ _ _
  dsimp only [centers] at hmembers
  unfold preparedCellGroupSourceWithWorkRaw preparedCellGroupSourceWithWork
  simp only [hmembers]
  simp only [Prod.map, id_eq, List.map_eq_nil_iff]
  split_ifs with h
  · rfl
  · rw [sampledGroupActionSourceWithWorkRaw_eq]

end OAI.EditApproximation.BinaryFraction
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_RawBandPipelineBridges
attribute [-simp] _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWorkRawBand OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedCellGroupSourceWithWorkRaw_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWorkRawBand OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWorkRawBand OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWorkRawBand OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedOnlineReadWithWorkRaw_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceWithWorkRawBand OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWorkRawBand OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWorkRawBand OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryLocalRefinementRawBand_eq : @OAI.EditApproximation.queryLocalRefinementRawBand = @OAI.EditApproximation.queryLocalRefinement := by
  unfold OAI.EditApproximation.queryLocalRefinementRawBand OAI.EditApproximation.queryLocalRefinement
  simp only [OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWorkRawBand_eq, OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryLocalRandomSourcesRawBand_eq : @OAI.EditApproximation.queryLocalRandomSourcesRawBand = @OAI.EditApproximation.queryLocalRandomSources := by
  unfold OAI.EditApproximation.queryLocalRandomSourcesRawBand OAI.EditApproximation.queryLocalRandomSources
  simp only [OAI.EditApproximation.queryLocalRefinementRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryLocalBandRawBand_eq : @OAI.EditApproximation.queryLocalBandRawBand = @OAI.EditApproximation.queryLocalBand := by
  unfold OAI.EditApproximation.queryLocalBandRawBand OAI.EditApproximation.queryLocalBand
  simp only [OAI.EditApproximation.queryLocalRandomSourcesRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryLocalProgramRawBand_eq : @OAI.EditApproximation.queryLocalProgramRawBand = @OAI.EditApproximation.queryLocalProgram := by
  unfold OAI.EditApproximation.queryLocalProgramRawBand OAI.EditApproximation.queryLocalProgram
  simp only [OAI.EditApproximation.queryLocalBandRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryPhysicalRandomDataRequestRawBand_eq : @OAI.EditApproximation.queryPhysicalRandomDataRequestRawBand = @OAI.EditApproximation.queryPhysicalRandomDataRequest := by
  unfold OAI.EditApproximation.queryPhysicalRandomDataRequestRawBand OAI.EditApproximation.queryPhysicalRandomDataRequest
  simp only [OAI.EditApproximation.queryLocalProgramRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryFamilyRefinementRawBand_eq : @OAI.EditApproximation.queryFamilyRefinementRawBand = @OAI.EditApproximation.queryFamilyRefinement := by
  unfold OAI.EditApproximation.queryFamilyRefinementRawBand OAI.EditApproximation.queryFamilyRefinement
  simp only [OAI.EditApproximation.queryPhysicalRandomDataRequestRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryFamilyActiveRawBand_eq : @OAI.EditApproximation.queryFamilyActiveRawBand = @OAI.EditApproximation.queryFamilyActive := by
  unfold OAI.EditApproximation.queryFamilyActiveRawBand OAI.EditApproximation.queryFamilyActive
  simp only [OAI.EditApproximation.queryFamilyRefinementRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryFamilyBoundedActiveRawBand_eq : @OAI.EditApproximation.queryFamilyBoundedActiveRawBand = @OAI.EditApproximation.queryFamilyBoundedActive := by
  unfold OAI.EditApproximation.queryFamilyBoundedActiveRawBand OAI.EditApproximation.queryFamilyBoundedActive
  simp only [OAI.EditApproximation.queryFamilyActiveRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryChargedFamilyTableRawBand_eq : @OAI.EditApproximation.queryChargedFamilyTableRawBand = @OAI.EditApproximation.queryChargedFamilyTable := by
  unfold OAI.EditApproximation.queryChargedFamilyTableRawBand OAI.EditApproximation.queryChargedFamilyTable
  simp only [OAI.EditApproximation.queryFamilyBoundedActiveRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryChargedFamilyGlobalRawBand_eq : @OAI.EditApproximation.queryChargedFamilyGlobalRawBand = @OAI.EditApproximation.queryChargedFamilyGlobal := by
  unfold OAI.EditApproximation.queryChargedFamilyGlobalRawBand OAI.EditApproximation.queryChargedFamilyGlobal
  simp only [OAI.EditApproximation.queryChargedFamilyTableRawBand_eq]
  rfl

@[simp] theorem OAI.EditApproximation.queryFamilyMemoRawRawBand_eq : @OAI.EditApproximation.queryFamilyMemoRawRawBand = @OAI.EditApproximation.queryFamilyMemoRaw := by
  unfold OAI.EditApproximation.queryFamilyMemoRawRawBand OAI.EditApproximation.queryFamilyMemoRaw
  simp only [OAI.EditApproximation.queryChargedFamilyGlobalRawBand_eq]

@[simp] theorem OAI.EditApproximation.computedQueryMemoRawRawBand_eq : @OAI.EditApproximation.computedQueryMemoRawRawBand = @OAI.EditApproximation.computedQueryMemoRaw := by
  unfold OAI.EditApproximation.computedQueryMemoRawRawBand OAI.EditApproximation.computedQueryMemoRaw
  simp only [OAI.EditApproximation.queryFamilyMemoRawRawBand_eq]

@[simp] theorem OAI.EditApproximation.computedQueryMemoNormalizedRawBand_eq : @OAI.EditApproximation.computedQueryMemoNormalizedRawBand = @OAI.EditApproximation.computedQueryMemoNormalized := by
  unfold OAI.EditApproximation.computedQueryMemoNormalizedRawBand OAI.EditApproximation.computedQueryMemoNormalized
  simp only [OAI.EditApproximation.computedQueryMemoRawRawBand_eq]

@[simp] theorem OAI.EditApproximation.computedQueryMemoResultRawBand_eq : @OAI.EditApproximation.computedQueryMemoResultRawBand = @OAI.EditApproximation.computedQueryMemoResult := by
  unfold OAI.EditApproximation.computedQueryMemoResultRawBand OAI.EditApproximation.computedQueryMemoResult
  simp only [OAI.EditApproximation.computedQueryMemoNormalizedRawBand_eq]

@[simp] theorem OAI.EditApproximation.computedQueryLocalWorkRawBand_eq : @OAI.EditApproximation.computedQueryLocalWorkRawBand = @OAI.EditApproximation.computedQueryLocalWork := by
  unfold OAI.EditApproximation.computedQueryLocalWorkRawBand OAI.EditApproximation.computedQueryLocalWork
  simp only [OAI.EditApproximation.computedQueryMemoNormalizedRawBand_eq]

@[simp] theorem OAI.EditApproximation.integerQueryLocalWorkRawBand_eq : @OAI.EditApproximation.integerQueryLocalWorkRawBand = @OAI.EditApproximation.integerQueryLocalWork := by
  unfold OAI.EditApproximation.integerQueryLocalWorkRawBand OAI.EditApproximation.integerQueryLocalWork
  simp only [OAI.EditApproximation.computedQueryLocalWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.computedQueryAnswerWithWorkRawBand_eq : @OAI.EditApproximation.computedQueryAnswerWithWorkRawBand = @OAI.EditApproximation.computedQueryAnswerWithWork := by
  unfold OAI.EditApproximation.computedQueryAnswerWithWorkRawBand OAI.EditApproximation.computedQueryAnswerWithWork
  simp only [OAI.EditApproximation.computedQueryMemoResultRawBand_eq]

@[simp] theorem OAI.EditApproximation.integerBinaryOutputRawBand_eq : @OAI.EditApproximation.integerBinaryOutputRawBand = @OAI.EditApproximation.integerBinaryOutput := by
  unfold OAI.EditApproximation.integerBinaryOutputRawBand OAI.EditApproximation.integerBinaryOutput
  simp only [OAI.EditApproximation.computedQueryAnswerWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.integerBinaryAnswerRawBand_eq : @OAI.EditApproximation.integerBinaryAnswerRawBand = @OAI.EditApproximation.integerBinaryAnswer := by
  unfold OAI.EditApproximation.integerBinaryAnswerRawBand OAI.EditApproximation.integerBinaryAnswer
  simp only [OAI.EditApproximation.integerBinaryOutputRawBand_eq]
  rfl

@[simp] theorem OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockRawBand_eq : @OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockRawBand = @OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlock := by
  unfold OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockRawBand OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlock
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.integerBinaryWorkRawBand_eq : @OAI.EditApproximation.integerBinaryWorkRawBand = @OAI.EditApproximation.integerBinaryWork := by
  unfold OAI.EditApproximation.integerBinaryWorkRawBand OAI.EditApproximation.integerBinaryWork
  simp only [OAI.EditApproximation.integerQueryLocalWorkRawBand_eq, OAI.EditApproximation.integerBinaryOutputRawBand_eq]

@[simp] theorem OAI.EditApproximation.integerFinalAllocationRawBand_eq : @OAI.EditApproximation.integerFinalAllocationRawBand = @OAI.EditApproximation.integerFinalAllocation := by
  unfold OAI.EditApproximation.integerFinalAllocationRawBand OAI.EditApproximation.integerFinalAllocation
  simp only [OAI.EditApproximation.computedQueryMemoResultRawBand_eq]
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_RawBandMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.EditApproximation
open Filter MeasureTheory
attribute [local instance] queryRoundsNeZero

theorem almostLinearEditDistanceRawBandV3_oai (epsilon : BinaryFraction)
    (hepsilon : 0 < epsilon.value) (_hepsilonOne : epsilon.value < 1)
    :
    (∀ (source target : List ℤ) (N : ℕ), source.length + target.length ≤ N →
      (2 / 3 : ℝ) ≤ (computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon).real
        {outcome | EditDistortion.edit source target ≤ integerBinaryAnswerRawBand source target N epsilon outcome ∧
          (integerBinaryAnswerRawBand source target N epsilon outcome : ℝ) ≤
            (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target}) ∧
    (∀ (source target : List ℤ) (N : ℕ), source = target → ∀ outcome,
      integerBinaryAnswerRawBand source target N epsilon outcome = 0) ∧
    (∀ (C : ℕ) (eta : ℝ), 0 < eta → ∀ᶠ N : ℕ in atTop,
      ∀ source target : List ℤ, source.length + target.length ≤ N →
        (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
        (∫ outcome, integerBinaryWorkRawBand source target N epsilon outcome
          ∂computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon) ≤
            (N + 2 : ℝ) ^ (1 + eta)) ∧
    (∀ C : ℕ, ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ,
      source.length + target.length ≤ N →
        (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
        ∀ outcome, integerBinarySpaceFootprintRawBand source target N epsilon outcome ≤ (N + 2) ^ (C + 65564)) := by
  simpa only [integerBinaryAnswerRawBand_eq, integerBinaryWorkRawBand_eq,
    integerBinarySpaceFootprintRawBand_eq] using
    almostLinearEditDistance_main epsilon hepsilon _hepsilonOne

end OAI.EditApproximation
end

theorem solution : type_of% @OAI.EditApproximation.almostLinearEditDistanceRawBandV3_oai := @OAI.EditApproximation.almostLinearEditDistanceRawBandV3_oai
