-- Prove2me | solution 1 for OAI.UniqueGamesTheorem.Foundations.Repetition.selectedRightProfileError_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:14:01.594206+00:00
-- url     : https://prove2.me/submissions/b5e209ec-aa5c-4b3e-83ee-2230bf165be6

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Std
import Definitions.Def_OAIQ252P011
import Theorems.Thm_OAI_UniqueGamesTheorem_Foundations_Repetition_selected_rightReveal_error_sum

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_Conditioning
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Conditioning of actual finite distributions and the selected-coordinate chain
rule used in parallel repetition. A normalized conditional distribution is only
constructed when the conditioning event has strictly positive probability.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

theorem probability_condition (μ : FiniteDistribution Ω) (given event : Ω → Bool)
    (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability event =
      μ.probability (fun x => given x && event x) / μ.probability given := by
  simp only [probability, condition, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hg : given x = true <;> by_cases he : event x = true <;> simp [hg, he]

@[simp] theorem probability_condition_given (μ : FiniteDistribution Ω)
    (given : Ω → Bool) (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability given = 1 := by
  rw [μ.probability_condition]
  simpa only [Bool.and_self] using div_self (ne_of_gt positive)

end FiniteDistribution

end

end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_SamplingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite real probability vectors and information inequalities.

`relativeEntropy` uses the natural logarithm and a real-valued finite sum.
Its theorems require support containment, so a positive numerator is never
silently assigned finite divergence against a zero denominator.
-/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem posterior_isProbability (p w : α → ℝ) (hp : IsProbability p)
    (hw : ∀ a, 0 ≤ w a) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ a, p a * w a = z) : IsProbability (posterior p w z) := by
  constructor
  · intro a
    exact div_nonneg (mul_nonneg (hp.1 a) (hw a)) hz.le
  · simp only [posterior, div_eq_mul_inv, ← Finset.sum_mul, hmass,
      mul_inv_cancel₀ hz.ne']

omit [Fintype α] in
theorem posterior_supportedBy (p w : α → ℝ) (z : ℝ) :
    SupportedBy (posterior p w z) p := by
  intro a ha hp
  exact ha (by simp [posterior, hp])

theorem mul_log_div_ge_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x - y ≤ x * Real.log (x / y) := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
  have hm := mul_le_mul_of_nonneg_left h hx.le
  have he : x * (1 - (x / y)⁻¹) = x - y := by
    field_simp [hx.ne', hy.ne']
  rwa [he] at hm

theorem relativeEntropy_nonneg (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) (hs : SupportedBy p q) : 0 ≤ relativeEntropy p q := by
  have hpoint : ∀ a, p a - q a ≤ p a * Real.log (p a / q a) := by
    intro a
    by_cases hpa : p a = 0
    · simp only [hpa, zero_sub, zero_div, zero_mul]
      exact neg_nonpos.mpr (hq.1 a)
    · exact mul_log_div_ge_sub (lt_of_le_of_ne (hp.1 a) (Ne.symm hpa))
        (lt_of_le_of_ne (hq.1 a) (Ne.symm (hs a hpa)))
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simpa [relativeEntropy, Finset.sum_sub_distrib, hp.2, hq.2] using hsum

theorem posterior_relativeEntropy_le (p w : α → ℝ) (hp : IsProbability p)
    (hw : ∀ a, 0 ≤ w a) (hw_one : ∀ a, w a ≤ 1) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ a, p a * w a = z) :
    relativeEntropy (posterior p w z) p ≤ Real.log (1 / z) := by
  have hpost := posterior_isProbability p w hp hw hz hmass
  have hpoint : ∀ a, posterior p w z a * Real.log (posterior p w z a / p a) ≤
      posterior p w z a * Real.log (1 / z) := by
    intro a
    by_cases hpa : posterior p w z a = 0
    · simp [hpa]
    have hpne := posterior_supportedBy p w z a hpa
    have hppos : 0 < p a := lt_of_le_of_ne (hp.1 a) (Ne.symm hpne)
    have hpostpos : 0 < posterior p w z a :=
      lt_of_le_of_ne (hpost.1 a) (Ne.symm hpa)
    have hr : posterior p w z a / p a = w a / z := by
      dsimp [posterior]
      field_simp [hpne, hz.ne']
    apply mul_le_mul_of_nonneg_left _ (hpost.1 a)
    apply Real.log_le_log (div_pos hpostpos hppos)
    rw [hr]
    exact div_le_div_of_nonneg_right (hw_one a) hz.le
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simpa only [relativeEntropy, ← Finset.sum_mul, hpost.2, one_mul] using hsum

end UniqueGamesTheorem.Foundations.Information

end

section

/-!
Conditional laws on finite spaces, with a normalized default on null rows.
The default remains a probability law when a new input law charges a row
that had zero probability in the original joint distribution.
-/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

theorem kernelProduct_isProbability
    (r : α → ℝ) (k : α → β → ℝ)
    (hr : IsProbability r) (hk : ∀ a, IsProbability (k a)) :
    IsProbability (fun ab : α × β => r ab.1 * k ab.1 ab.2) := by
  constructor
  · intro ab
    exact mul_nonneg (hr.1 ab.1) ((hk ab.1).1 ab.2)
  · simp only [Fintype.sum_prod_type, ← Finset.mul_sum,
      (hk _).2, mul_one, hr.2]

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Statistical distance under finite kernels and event restriction. -/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

theorem totalVariation_joint_common_kernel (p q : α → ℝ) (k : α → β → ℝ)
    (hk : ∀ a, IsProbability (k a)) :
    totalVariation (fun ab : α × β => p ab.1 * k ab.1 ab.2)
      (fun ab : α × β => q ab.1 * k ab.1 ab.2) = totalVariation p q := by
  have hpoint : ∀ a b, |p a * k a b - q a * k a b| = |p a - q a| * k a b := by
    intro a b
    rw [← sub_mul, abs_mul, abs_of_nonneg ((hk a).1 b)]
  simp only [totalVariation, Fintype.sum_prod_type, hpoint, ← Finset.mul_sum,
    (hk _).2, mul_one]

end UniqueGamesTheorem.Foundations.Information

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_PinskerLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
A finite Pinsker inequality with a nonoptimal constant, sufficient for the
information bound used by Holenstein: TV(p,q)^2 ≤ D_nat(p || q).
The proof factors the L1 distance through square roots and uses log t ≤ t-1.
-/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem sqrt_distance_le_relativeEntropy_term {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hs : x ≠ 0 → y ≠ 0) :
    (Real.sqrt x - Real.sqrt y)^2 ≤ x * Real.log (x / y) - x + y := by
  by_cases hxzero : x = 0
  · subst x
    simp [Real.sq_sqrt hy]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm (hs hxzero))
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hypos
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsy hsx)
  have hlogid : Real.log (Real.sqrt y / Real.sqrt x) =
      -(Real.log (x / y)) / 2 := by
    rw [Real.log_div hsy.ne' hsx.ne', Real.log_sqrt hy, Real.log_sqrt hx,
      Real.log_div hxzero (hs hxzero)]
    ring
  have hprod : x * (Real.sqrt y / Real.sqrt x) = Real.sqrt x * Real.sqrt y := by
    calc
      x * (Real.sqrt y / Real.sqrt x) = (Real.sqrt x)^2 * (Real.sqrt y / Real.sqrt x) := by
        rw [Real.sq_sqrt hx]
      _ = Real.sqrt x * Real.sqrt y := by field_simp [hsx.ne']
  have hm := mul_le_mul_of_nonneg_left hlog hx
  rw [hlogid, mul_sub, mul_one, hprod] at hm
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]

theorem hellingerSquared_le_relativeEntropy (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) (hs : SupportedBy p q) :
    hellingerSquared p q ≤ relativeEntropy p q := by
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) =>
    sqrt_distance_le_relativeEntropy_term (hp.1 a) (hq.1 a) (hs a))
  simpa only [hellingerSquared, relativeEntropy, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hp.2, hq.2, sub_add_cancel] using hsum

theorem totalVariation_sq_le_hellingerSquared (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) : totalVariation p q ^ 2 ≤ hellingerSquared p q := by
  have hfactor : ∀ a, |Real.sqrt (p a) - Real.sqrt (q a)| *
      (Real.sqrt (p a) + Real.sqrt (q a)) = |p a - q a| := by
    intro a
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
      ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt (hp.1 a), Real.sq_sqrt (hq.1 a)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun a => |Real.sqrt (p a) - Real.sqrt (q a)|)
    (fun a => Real.sqrt (p a) + Real.sqrt (q a))
  simp only [hfactor, sq_abs] at hcs
  have hpoint : ∀ a, (Real.sqrt (p a) + Real.sqrt (q a)) ^ 2 ≤ 2 * (p a + q a) := by
    intro a
    nlinarith [sq_nonneg (Real.sqrt (p a) - Real.sqrt (q a)),
      Real.sq_sqrt (hp.1 a), Real.sq_sqrt (hq.1 a)]
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, hp.2, hq.2] at hsum
  have hnonneg : 0 ≤ ∑ a, (Real.sqrt (p a) - Real.sqrt (q a)) ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hsum hnonneg
  dsimp [totalVariation, hellingerSquared]
  nlinarith

theorem totalVariation_sq_le_relativeEntropy (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) (hs : SupportedBy p q) :
    totalVariation p q ^ 2 ≤ relativeEntropy p q :=
  (totalVariation_sq_le_hellingerSquared p q hp hq).trans
    (hellingerSquared_le_relativeEntropy p q hp hq hs)

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Tensorization and conditioning for finite independent coordinates. -/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]

theorem coordinateMarginal_isProbability (p : (ι → α) → ℝ) (hp : IsProbability p) (i : ι) :
    IsProbability (coordinateMarginal p i) := by
  classical
  constructor
  · intro a
    apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact hp.1 x
    · exact le_rfl
  · simp only [coordinateMarginal]
    rw [Finset.sum_comm]
    simpa using hp.2

theorem point_le_coordinateMarginal (p : (ι → α) → ℝ) (hp : IsProbability p)
    (i : ι) (x : ι → α) : p x ≤ coordinateMarginal p i (x i) := by
  classical
  have h := Finset.single_le_sum
    (f := fun y : ι → α => if y i = x i then p y else 0)
    (fun y _ => by split_ifs; exact hp.1 y; exact le_rfl) (Finset.mem_univ x)
  simpa [coordinateMarginal] using h

theorem marginal_expectation (p : (ι → α) → ℝ) (i : ι) (f : α → ℝ) :
    (∑ x, p x * f (x i)) = ∑ a, coordinateMarginal p i a * f a := by
  classical
  simp only [coordinateMarginal, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

theorem joint_supportedBy_product_coordinateMarginals (p : (ι → α) → ℝ)
    (hp : IsProbability p) : SupportedBy p (independentProduct (coordinateMarginal p)) := by
  intro x hx
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact ne_of_gt ((lt_of_le_of_ne (hp.1 x) (Ne.symm hx)).trans_le
    (point_le_coordinateMarginal p hp i x))

theorem relativeEntropy_independent_reference (p : (ι → α) → ℝ) (q : ι → α → ℝ)
    (hp : IsProbability p) (_hq : ∀ i, IsProbability (q i))
    (hs : ∀ i, SupportedBy (coordinateMarginal p i) (q i)) :
    relativeEntropy p (independentProduct q) =
      relativeEntropy p (independentProduct (coordinateMarginal p)) +
        ∑ i, relativeEntropy (coordinateMarginal p i) (q i) := by
  classical
  have hpoint : ∀ x : ι → α, p x * Real.log (p x / independentProduct q x) =
      p x * Real.log (p x / independentProduct (coordinateMarginal p) x) +
        ∑ i, p x * Real.log (coordinateMarginal p i (x i) / q i (x i)) := by
    intro x
    by_cases hx : p x = 0
    · simp [hx]
    have hm : ∀ i, coordinateMarginal p i (x i) ≠ 0 := by
      intro i
      exact ne_of_gt ((lt_of_le_of_ne (hp.1 x) (Ne.symm hx)).trans_le
        (point_le_coordinateMarginal p hp i x))
    have hqne : ∀ i, q i (x i) ≠ 0 := fun i => hs i (x i) (hm i)
    have hmp : (∏ i, coordinateMarginal p i (x i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hm i)
    have hqp : (∏ i, q i (x i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hqne i)
    simp only [independentProduct, Real.log_div hx hmp, Real.log_div hx hqp,
      Real.log_prod (fun i _ => hm i), Real.log_prod (fun i _ => hqne i)]
    simp_rw [Real.log_div (hm _) (hqne _)]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  calc
    relativeEntropy p (independentProduct q) =
        ∑ x, (p x * Real.log (p x / independentProduct (coordinateMarginal p) x) +
          ∑ i, p x * Real.log (coordinateMarginal p i (x i) / q i (x i))) := by
      exact Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = relativeEntropy p (independentProduct (coordinateMarginal p)) +
        ∑ i, ∑ x, p x * Real.log (coordinateMarginal p i (x i) / q i (x i)) := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      rfl
    _ = relativeEntropy p (independentProduct (coordinateMarginal p)) +
        ∑ i, relativeEntropy (coordinateMarginal p i) (q i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact marginal_expectation p i (fun a => Real.log (coordinateMarginal p i a / q i a))

theorem coordinate_relativeEntropy_sum_le (p : (ι → α) → ℝ) (q : ι → α → ℝ)
    (hp : IsProbability p) (hq : ∀ i, IsProbability (q i))
    (hs : ∀ i, SupportedBy (coordinateMarginal p i) (q i)) :
    (∑ i, relativeEntropy (coordinateMarginal p i) (q i)) ≤
      relativeEntropy p (independentProduct q) := by
  rw [relativeEntropy_independent_reference p q hp hq hs]
  exact le_add_of_nonneg_left (relativeEntropy_nonneg _ _ hp
    (independentProduct_isProbability _ (coordinateMarginal_isProbability p hp))
    (joint_supportedBy_product_coordinateMarginals p hp))

theorem coordinate_totalVariation_sq_sum_le (p : (ι → α) → ℝ) (q : ι → α → ℝ)
    (hp : IsProbability p) (hq : ∀ i, IsProbability (q i))
    (hs : ∀ i, SupportedBy (coordinateMarginal p i) (q i)) :
    (∑ i, totalVariation (coordinateMarginal p i) (q i) ^ 2) ≤
      relativeEntropy p (independentProduct q) := by
  exact (Finset.sum_le_sum (fun i _ => totalVariation_sq_le_relativeEntropy _ _
    (coordinateMarginal_isProbability p hp i) (hq i) (hs i))).trans
      (coordinate_relativeEntropy_sum_le p q hp hq hs)

theorem posterior_coordinate_supportedBy (q : ι → α → ℝ) (w : (ι → α) → ℝ)
    (z : ℝ) (i : ι) :
    SupportedBy (coordinateMarginal (posterior (independentProduct q) w z) i) (q i) := by
  classical
  intro a ha hqa
  apply ha
  unfold coordinateMarginal
  apply Finset.sum_eq_zero
  intro x _
  by_cases hxa : x i = a
  · have hzprod : independentProduct q x = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa only [hxa] using hqa)
    simp [hxa, posterior, hzprod]
  · simp [hxa]

/-- The finite independent-coordinate conditioning inequality underlying
Holenstein Lemma 4.1, with natural logarithms. `w x` is the conditional
probability of the event given the coordinate tuple `x`. -/
theorem posterior_coordinate_totalVariation_sq_sum_le_log
    (q : ι → α → ℝ) (hq : ∀ i, IsProbability (q i)) (w : (ι → α) → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw_one : ∀ x, w x ≤ 1) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ x, independentProduct q x * w x = z) :
    (∑ i, totalVariation
      (coordinateMarginal (posterior (independentProduct q) w z) i) (q i) ^ 2) ≤
        Real.log (1 / z) := by
  have hp := independentProduct_isProbability q hq
  exact (coordinate_totalVariation_sq_sum_le _ q
    (posterior_isProbability _ w hp hw hz hmass) hq
    (posterior_coordinate_supportedBy q w z)).trans
      (posterior_relativeEntropy_le _ w hp hw hw_one hz hmass)

end UniqueGamesTheorem.Foundations.Information

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_FactorizationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Replacing the input marginal of an actual conditional profile. -/
namespace UniqueGamesTheorem.Foundations.Repetition.ProfileCorrection
open scoped BigOperators
open UniqueGamesTheorem.Foundations.Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

omit [Fintype X] in
theorem seedQuestionMarginal_first (p : X × (S × Y) → ℝ) :
    firstMarginal (seedQuestionMarginal p) = firstMarginal p := by
  funext x
  simp only [seedQuestionMarginal, firstMarginal, Fintype.sum_prod_type]

theorem totalVariation_triangle {Ω : Type*} [Fintype Ω]
    (p c d : Ω → ℝ) :
    totalVariation p d ≤ totalVariation p c + totalVariation c d := by
  unfold totalVariation
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => abs_sub_le (p x) (c x) (d x))
  rw [Finset.sum_add_distrib] at h
  linarith

theorem left_profile_correction
    (p : X × (S × Y) → ℝ) (μ : X × Y → ℝ)
    (fallbackS : S → ℝ) (fallbackY : Y → ℝ)
    (hp : IsProbability p) (hμ : IsProbability μ)
    (hS : IsProbability fallbackS) (hY : IsProbability fallbackY) :
    totalVariation p (fun z => μ (z.1, z.2.2) *
      conditionalKernel (seedQuestionMarginal p) fallbackS z.1 z.2.1) ≤
    totalVariation p (fun z => seedQuestionMarginal p (z.1, z.2.1) *
      conditionalKernel μ fallbackY z.1 z.2.2) +
    totalVariation (firstMarginal p) (firstMarginal μ) := by
  let σ := seedQuestionMarginal p
  let L := conditionalKernel σ fallbackS
  let M := conditionalKernel μ fallbackY
  let k : X → S × Y → ℝ := fun x sy => L x sy.1 * M x sy.2
  let c : X × (S × Y) → ℝ := fun z => σ (z.1,z.2.1) * M z.1 z.2.2
  let d : X × (S × Y) → ℝ := fun z => μ (z.1,z.2.2) * L z.1 z.2.1
  have hσ : IsProbability σ := seedQuestionMarginal_isProbability p hp
  have hk : ∀ x, IsProbability (k x) := by
    intro x
    exact kernelProduct_isProbability (L x) (fun _ : S => M x)
      (conditionalKernel_isProbability σ fallbackS hσ hS x)
      (fun _ => conditionalKernel_isProbability μ fallbackY hμ hY x)
  have hc : c = fun z => firstMarginal σ z.1 * k z.1 z.2 := by
    funext z
    change σ (z.1,z.2.1) * M z.1 z.2.2 =
      firstMarginal σ z.1 * (L z.1 z.2.1 * M z.1 z.2.2)
    rw [← mul_assoc, marginal_mul_conditionalKernel σ fallbackS hσ]
  have hd : d = fun z => firstMarginal μ z.1 * k z.1 z.2 := by
    funext z
    change μ (z.1,z.2.2) * L z.1 z.2.1 =
      firstMarginal μ z.1 * (L z.1 z.2.1 * M z.1 z.2.2)
    calc
      _ = (firstMarginal μ z.1 * M z.1 z.2.2) * L z.1 z.2.1 := by
        rw [marginal_mul_conditionalKernel μ fallbackY hμ]
      _ = _ := by ring
  have hmiddle : totalVariation c d =
      totalVariation (firstMarginal σ) (firstMarginal μ) := by
    rw [hc, hd]
    exact totalVariation_joint_common_kernel _ _ k hk
  have result := totalVariation_triangle p c d
  rw [hmiddle] at result
  have hmarg : firstMarginal σ = firstMarginal p := seedQuestionMarginal_first p
  rw [hmarg] at result
  exact result
end
end UniqueGamesTheorem.Foundations.Repetition.ProfileCorrection

end

section

/-! The actual single-coordinate dependency-breaking reveal distribution.
The tag records which endpoint of the question pair was revealed. -/

namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem revealInputLaw_inl (μ : FiniteDistribution (X × Y)) (x : X) :
    (revealInputLaw μ).weight (Sum.inl x) = (∑ y, μ.weight (x,y)) / 2 := by
  classical
  rw [revealInputLaw_weight]
  simp [firstMarginal, Fintype.sum_prod_type, revealLaw_weight, div_eq_mul_inv]
  rw [Finset.sum_comm]
  simp [← Finset.sum_mul]

theorem revealInputLaw_inr (μ : FiniteDistribution (X × Y)) (y : Y) :
    (revealInputLaw μ).weight (Sum.inr y) = (∑ x, μ.weight (x,y)) / 2 := by
  classical
  rw [revealInputLaw_weight]
  simp [firstMarginal, Fintype.sum_prod_type, revealLaw_weight,
    div_eq_mul_inv, ← Finset.sum_mul]

theorem revealProfile_inl_diagonal (μ : FiniteDistribution (X × Y)) (x : X) (y : Y) :
    (revealProfile μ (Sum.inl x)).weight (x,y) =
      conditionalKernel μ.weight (μ.pushforward Prod.snd).weight x y := by
  classical
  have hm : firstMarginal (revealFirstLaw μ).weight (Sum.inl x) =
      firstMarginal μ.weight x / 2 := by
    rw [← revealInputLaw_weight, revealInputLaw_inl]
    rfl
  have hf : (revealFallback μ (Sum.inl x)).weight (x,y) =
      (μ.pushforward Prod.snd).weight y := by
    simp [revealFallback, FiniteDistribution.pushforward, Prod.mk.injEq]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q.2 = y <;> simp [hq]
  simp only [revealProfile, gameConditionalKernel, toGameLaw, conditionalKernel, hm]
  by_cases h : firstMarginal μ.weight x = 0
  · simpa [h] using hf
  · have hh : firstMarginal μ.weight x / 2 ≠ 0 := div_ne_zero h (by norm_num)
    simp only [ite_eq_right h, ite_eq_right hh, revealFirstLaw_weight, revealLaw_weight,
      ite_true, if_true, Sum.inl_ne_inr, ite_false, if_false, add_zero]
    field_simp

theorem revealProfile_inr_diagonal (μ : FiniteDistribution (X × Y)) (x : X) (y : Y) :
    (revealProfile μ (Sum.inr y)).weight (x,y) =
      conditionalKernel (μ.transport (Equiv.prodComm X Y)).weight
        (μ.pushforward Prod.fst).weight y x := by
  classical
  have hm : firstMarginal (revealFirstLaw μ).weight (Sum.inr y) =
      firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y / 2 := by
    rw [← revealInputLaw_weight, revealInputLaw_inr]
    rfl
  have hf : (revealFallback μ (Sum.inr y)).weight (x,y) =
      (μ.pushforward Prod.fst).weight x := by
    simp [revealFallback, FiniteDistribution.pushforward, Prod.mk.injEq]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q.1 = x <;> simp [hq]
  simp only [revealProfile, gameConditionalKernel, toGameLaw, conditionalKernel, hm]
  by_cases h : firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y = 0
  · simpa [h] using hf
  · have hh : firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y / 2 ≠ 0 :=
      div_ne_zero h (by norm_num)
    simp only [ite_eq_right h, ite_eq_right hh, revealFirstLaw_weight, revealLaw_weight,
      ite_true, if_true, Sum.inr_ne_inl, ite_false, if_false, zero_add]
    change (μ.weight (x,y) / 2) / (firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y / 2) =
      μ.weight (x,y) / firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y
    field_simp

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_FinishBoundsLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.probability_condition_given _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact composition identities for finite distribution maps. -/
namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

theorem weight_eq_probability_singleton [DecidableEq A] (μ : FiniteDistribution A) (a : A) :
    μ.weight a = μ.probability (fun x => decide (x = a)) := by
  classical
  simp [probability]

theorem pushforward_comp (μ : FiniteDistribution A) (f : A → B) (g : B → C) :
    (μ.pushforward f).pushforward g = μ.pushforward (fun a => g (f a)) := by
  classical
  apply eq_of_weight_eq
  intro c
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton]
  simp only [probability_pushforward]

theorem transport_eq_pushforward (μ : FiniteDistribution A) (e : A ≃ B) :
    μ.transport e = μ.pushforward e := by
  classical
  apply eq_of_weight_eq
  intro b
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton,
    probability_transport, probability_pushforward]

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_SelectedInformationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OccurrenceGame.toGame_success _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.restrict_extend _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.success_restrict _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.wins_restrict _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.PerfectCompleteness.SourceGame.questionGame_success _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Conditioning bounds for the actual repeated-game question marginals.
The likelihood and its normalizer are derived from the selected-win event.
The final estimate retains only the unselected coordinates. -/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games Information

noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedTupleLikelihood_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : Fin n → Q₁ × Q₂) :
    0 ≤ selectedTupleLikelihood G strategy selected questions := by
  unfold selectedTupleLikelihood
  split <;> norm_num

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedTupleLikelihood_le_one (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : Fin n → Q₁ × Q₂) :
    selectedTupleLikelihood G strategy selected questions ≤ 1 := by
  unfold selectedTupleLikelihood
  split <;> norm_num

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedTupleLikelihood_mass (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    (∑ questions, independentProduct (fun _ : Fin n => G.questions.weight) questions *
      selectedTupleLikelihood G strategy selected questions) =
        G.selectedSuccess strategy selected := by
  classical
  change _ = ((G.questions.iid n).transport (Game.tupleQuestionEquiv n)).probability
    (G.selectedWins strategy selected)
  rw [FiniteDistribution.probability_transport]
  simp only [FiniteDistribution.probability, FiniteDistribution.iid, independentProduct,
    selectedTupleLikelihood, mul_ite, mul_one, mul_zero]

theorem selectedQuestionMarginal_weight (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (i : Fin n) :
    (selectedQuestionMarginal G strategy selected positive i).weight =
      coordinateMarginal
        (posterior (independentProduct (fun _ : Fin n => G.questions.weight))
          (selectedTupleLikelihood G strategy selected) (G.selectedSuccess strategy selected)) i := by
  classical
  funext a
  simp only [selectedQuestionMarginal, FiniteDistribution.pushforward,
    FiniteDistribution.condition, coordinateMarginal]
  refine Fintype.sum_equiv (Game.tupleQuestionEquiv (Q₁ := Q₁) (Q₂ := Q₂) n).symm _ _ ?_
  intro questions
  cases he : G.selectedWins strategy selected questions <;>
    simp [Game.repetition_question_weight, Game.tupleQuestionEquiv,
      posterior, independentProduct, selectedTupleLikelihood, Game.selectedSuccess, he]

/-- The full-coordinate squared-distance bound specialized to the actual game
and actual selected event. -/
theorem selectedQuestionMarginal_totalVariation_sq_sum_le_log
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ i : Fin n,
      (selectedQuestionMarginal G strategy selected positive i).totalVariation G.questions ^ 2) ≤
        Real.log (1 / G.selectedSuccess strategy selected) := by
  classical
  change (∑ i : Fin n, Information.totalVariation
    (selectedQuestionMarginal G strategy selected positive i).weight G.questions.weight ^ 2) ≤ _
  simp_rw [selectedQuestionMarginal_weight]
  exact posterior_coordinate_totalVariation_sq_sum_le_log
    (fun _ : Fin n => G.questions.weight) (fun _ => gameLaw_isProbability G.questions)
    (selectedTupleLikelihood G strategy selected)
    (selectedTupleLikelihood_nonnegative G strategy selected)
    (selectedTupleLikelihood_le_one G strategy selected)
    positive (selectedTupleLikelihood_mass G strategy selected)

/-- Restricting to the unused coordinates does not spend any further
information budget. -/
theorem unselectedQuestionMarginal_totalVariation_sq_sum_le_log
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ i : {i : Fin n // i ∉ selected},
      (selectedQuestionMarginal G strategy selected positive i.1).totalVariation G.questions ^ 2) ≤
        Real.log (1 / G.selectedSuccess strategy selected) := by
  classical
  let d : Fin n → ℝ := fun i =>
    (selectedQuestionMarginal G strategy selected positive i).totalVariation G.questions
  have hfull := selectedQuestionMarginal_totalVariation_sq_sum_le_log G strategy selected positive
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => i ∈ selected)
    (fun i => d i ^ 2)
  have hinst : Subtype.fintype (fun i : Fin n => i ∈ selected) =
      Finset.Subtype.fintype selected := Subsingleton.elim _ _
  rw [hinst] at hsplit
  have hselected : 0 ≤ ∑ i : {i : Fin n // i ∈ selected}, d i.1 ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change (∑ i : {i : Fin n // i ∉ selected}, d i.1 ^ 2) ≤ _
  change (∑ i : Fin n, d i ^ 2) ≤ _ at hfull
  linarith

/-- The marginal-pair term used in Holenstein's dependency-breaking argument.
The estimate is valid also when there are no unused coordinates. -/
theorem unselectedQuestionMarginal_totalVariation_sum_le_sqrt
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ i : {i : Fin n // i ∉ selected},
      (selectedQuestionMarginal G strategy selected positive i.1).totalVariation G.questions) ≤
        Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
          Real.log (1 / G.selectedSuccess strategy selected)) := by
  classical
  let d : {i : Fin n // i ∉ selected} → ℝ := fun i =>
    (selectedQuestionMarginal G strategy selected positive i.1).totalVariation G.questions
  have hsq := unselectedQuestionMarginal_totalVariation_sq_sum_le_log G strategy selected positive
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset {i : Fin n // i ∉ selected}) d (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  have hln : 0 ≤ Real.log (1 / G.selectedSuccess strategy selected) :=
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)).trans hsq
  have hcard : 0 ≤ (Fintype.card {i : Fin n // i ∉ selected} : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsq hcard
  have hsqrt := Real.sq_sqrt (mul_nonneg hcard hln)
  have hsqrtpos := Real.sqrt_nonneg
    ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
      Real.log (1 / G.selectedSuccess strategy selected))
  change (∑ i, d i) ≤ _
  change (∑ i, d i ^ 2) ≤ _ at hsq
  change (Fintype.card {i : Fin n // i ∉ selected} : ℝ) * (∑ i, d i ^ 2) ≤ _ at hmul
  nlinarith

end

end UniqueGamesTheorem.Foundations.Repetition

end

section

/-!
Identification of the auxiliary selected-answer/reveal law with the actual
repeated-game question law conditioned on selected-coordinate success.
The proof sums out answer labels and reveal variables before merging the
selected and unselected question coordinates.
-/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedSplit_question_probability (G : Game Q₁ Q₂ A₁ A₂)
    (selected : Finset (Fin n))
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (selectedSplitLaw G selected).probability
      (fun q => event (selectedQuestionTuple selected q.1 q.2)) =
        (G.repetition n).questions.probability event := by
  rw [selectedSplitLaw, ← iid_coordinate_split, FiniteDistribution.probability_transport]
  change (G.questions.iid n).probability _ =
    ((G.questions.iid n).transport (Game.tupleQuestionEquiv n)).probability event
  rw [FiniteDistribution.probability_transport]
  apply congrArg (G.questions.iid n).probability
  funext q
  congr 1
  apply Prod.ext <;> funext i <;>
    simp [selectedQuestionTuple, coordinateSplitEquiv, mergeCoordinates, Game.tupleQuestionEquiv]

/-- Marginalizing the actual likelihood against any question event gives
the joint probability of selected-coordinate success and that event. -/
theorem selectedJoint_eventMass (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (∑ tv : SelectedInput Q₁ Q₂ selected ×
        SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
      (selectedInputLaw G selected).weight tv.1 *
        ∑ u, independentProduct
          (fun i => (selectedInputProfile G selected tv.1 i).weight) u *
            selectedLikelihood G strategy selected tv.1.1 tv.2 u *
              (if event (selectedQuestionTuple selected tv.1.1 u) then 1 else 0)) =
      (G.repetition n).questions.probability
        (fun q => G.selectedWins strategy selected q && event q) := by
  classical
  have hlabel (t : SelectedInput Q₁ Q₂ selected) :
      (∑ v, ∑ u, independentProduct
        (fun i => (selectedInputProfile G selected t i).weight) u *
          selectedLikelihood G strategy selected t.1 v u *
            (if event (selectedQuestionTuple selected t.1 u) then 1 else 0)) =
      ∑ u, independentProduct
        (fun i => (selectedInputProfile G selected t i).weight) u *
          (if G.selectedWins strategy selected (selectedQuestionTuple selected t.1 u) &&
            event (selectedQuestionTuple selected t.1 u) then 1 else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [← Finset.sum_mul, ← Finset.mul_sum, selectedLikelihood_sum]
    cases hw : G.selectedWins strategy selected (selectedQuestionTuple selected t.1 u) <;>
      cases he : event (selectedQuestionTuple selected t.1 u) <;> simp
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hlabel]
  rw [Fintype.sum_prod_type]
  simp only [selectedInputLaw, FiniteDistribution.product, FiniteDistribution.table,
    selectedInputProfile, independentProduct]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hforget (fixed : selected → Q₁ × Q₂) :=
    reveal_product_expectation G.questions
      (fun u : {i : Fin n // i ∉ selected} → Q₁ × Q₂ =>
        if G.selectedWins strategy selected (selectedQuestionTuple selected fixed u) &&
          event (selectedQuestionTuple selected fixed u) then (1 : ℝ) else 0)
  simp_rw [hforget]
  have h := selectedSplit_question_probability G selected
    (fun q => G.selectedWins strategy selected q && event q)
  simpa [selectedSplitLaw, FiniteDistribution.probability, FiniteDistribution.product,
    FiniteDistribution.table, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_assoc] using h

theorem selectedJointLaw_question_probability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (selectedJointLaw G strategy selected positive).probability
      (fun z => event (selectedQuestionTuple selected z.1.1.1 z.2)) =
        ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
          event := by
  classical
  erw [FiniteDistribution.probability_condition]
  change
    (∑ z : (SelectedInput Q₁ Q₂ selected ×
        SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
          ({i : Fin n // i ∉ selected} → Q₁ × Q₂),
      if event (selectedQuestionTuple selected z.1.1.1 z.2)
      then selectedJointWeight G strategy selected z else 0) =
        (G.repetition n).questions.probability
          (fun q => G.selectedWins strategy selected q && event q) /
            G.selectedSuccess strategy selected
  calc
    _ = (∑ tv : SelectedInput Q₁ Q₂ selected ×
          SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
        (selectedInputLaw G selected).weight tv.1 *
          ∑ u, independentProduct
            (fun i => (selectedInputProfile G selected tv.1 i).weight) u *
              selectedLikelihood G strategy selected tv.1.1 tv.2 u *
                (if event (selectedQuestionTuple selected tv.1.1 u) then 1 else 0)) /
        G.selectedSuccess strategy selected := by
      conv_lhs => rw [Fintype.sum_prod_type]
      simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tv _
      apply Finset.sum_congr rfl
      intro u _
      cases he : event (selectedQuestionTuple selected tv.1.1 u) <;>
        simp [selectedJointWeight, div_eq_mul_inv, mul_assoc]
    _ = _ := by rw [selectedJoint_eventMass]

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_PartialRevealLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Removing one independent reveal from the explicit product law. The
likelihood can be any function of the questions and outside data. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
noncomputable section
variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem totalVariation_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p q : B → ℝ) :
    Information.totalVariation (fun a => p (e a)) (fun a => q (e a)) =
      Information.totalVariation p q := by
  unfold Information.totalVariation
  congr 1
  exact e.sum_comp (fun b => |p b - q b|)

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! Conditional common-data profiles, with their error measured against the
actual endpoint-reveal reference and the actual question marginal. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

theorem firstMarginal_totalVariation_le (r t : X × Y → ℝ) :
    totalVariation (firstMarginal r) (firstMarginal t) ≤ totalVariation r t := by
  unfold totalVariation firstMarginal
  simp_rw [← Finset.sum_sub_distrib]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => Finset.abs_sum_le_sum_abs (fun y : Y => r (x,y)-t (x,y)) Finset.univ)
  rw [Fintype.sum_prod_type]
  linarith

theorem leftCommonProfile_error [DecidableEq X] [DecidableEq Y]
    (p : S × (X × Y) → ℝ) (μ : FiniteDistribution (X × Y)) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) :
    totalVariation p (fun z => μ.weight z.2 * leftCommonProfile p fallback z.2.1 z.1) ≤
      totalVariation p (leftRevealModel μ p) + totalVariation (secondMarginal p) μ.weight := by
  let e := swapSeedLeft (S := S) (X := X) (Y := Y)
  let p' : X × (S × Y) → ℝ := fun z => p (e z)
  have h := ProfileCorrection.left_profile_correction p' μ.weight fallback
    (μ.pushforward Prod.snd).weight
    (isProbability_comp_equiv e p hp) (gameLaw_isProbability μ) hf
    (gameLaw_isProbability (μ.pushforward Prod.snd))
  have hs : ProfileCorrection.seedQuestionMarginal p' = leftCommonMarginal p := rfl
  have hc : (fun z : X × (S × Y) => ProfileCorrection.seedQuestionMarginal p' (z.1,z.2.1) *
      conditionalKernel μ.weight (μ.pushforward Prod.snd).weight z.1 z.2.2) =
      fun z => leftRevealModel μ p (e z) := by
    funext z
    change (∑ y, p (z.2.1,(z.1,y))) *
      conditionalKernel μ.weight (μ.pushforward Prod.snd).weight z.1 z.2.2 =
      (∑ y, p (z.2.1,(z.1,y))) *
        (revealProfile μ (Sum.inl z.1)).weight (z.1,z.2.2)
    rw [revealProfile_inl_diagonal]
  have hd : (fun z : X × (S × Y) => μ.weight (z.1,z.2.2) *
      conditionalKernel (ProfileCorrection.seedQuestionMarginal p') fallback z.1 z.2.1) =
      fun z => μ.weight (e z).2 * leftCommonProfile p fallback (e z).2.1 (e z).1 := rfl
  rw [hc, hd] at h
  change totalVariation (fun z => p (e z)) _ ≤
    totalVariation (fun z => p (e z)) _ + _ at h
  rw [totalVariation_comp_equiv e p (leftRevealModel μ p)] at h
  rw [totalVariation_comp_equiv e p
    (fun z => μ.weight z.2 * leftCommonProfile p fallback z.2.1 z.1)] at h
  have hm : firstMarginal p' = firstMarginal (secondMarginal p) := by
    funext x
    simp only [firstMarginal, secondMarginal, Fintype.sum_prod_type, p', e, swapSeedLeft]
    exact Finset.sum_comm
  rw [hm] at h
  exact h.trans (add_le_add le_rfl (firstMarginal_totalVariation_le (secondMarginal p) μ.weight))

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

theorem swap_question_pushforward_snd (μ : FiniteDistribution (X × Y)) :
    ((μ.transport (Equiv.prodComm X Y)).pushforward Prod.snd) = μ.pushforward Prod.fst := by
  rw [FiniteDistribution.transport_eq_pushforward, FiniteDistribution.pushforward_comp]
  rfl

omit [Fintype S] in
theorem leftRevealModel_swap [DecidableEq X] [DecidableEq Y]
    (p : S × (X × Y) → ℝ) (μ : FiniteDistribution (X × Y)) (z : S × (Y × X)) :
    leftRevealModel (μ.transport (Equiv.prodComm X Y))
      (fun z => p (swapQuestionEndpoints z)) z = rightRevealModel μ p (swapQuestionEndpoints z) := by
  rcases z with ⟨s,y,x⟩
  change (∑ x', p (s,(x',y))) *
      (revealProfile (μ.transport (Equiv.prodComm X Y)) (Sum.inl y)).weight (y,x) =
    (∑ x', p (s,(x',y))) * (revealProfile μ (Sum.inr y)).weight (x,y)
  rw [revealProfile_inl_diagonal, revealProfile_inr_diagonal, swap_question_pushforward_snd]

theorem rightCommonProfile_error [DecidableEq X] [DecidableEq Y]
    (p : S × (X × Y) → ℝ) (μ : FiniteDistribution (X × Y)) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) :
    totalVariation p (fun z => μ.weight z.2 * rightCommonProfile p fallback z.2.2 z.1) ≤
      totalVariation p (rightRevealModel μ p) + totalVariation (secondMarginal p) μ.weight := by
  let e := swapQuestionEndpoints (S := S) (X := X) (Y := Y)
  let p' : S × (Y × X) → ℝ := fun z => p (e z)
  let μ' := μ.transport (Equiv.prodComm X Y)
  have h := leftCommonProfile_error p' μ' fallback (isProbability_comp_equiv e p hp) hf
  have hc : leftRevealModel μ' p' = fun z => rightRevealModel μ p (e z) := by
    funext z
    exact leftRevealModel_swap p μ z
  have hd : (fun z : S × (Y × X) => μ'.weight z.2 * leftCommonProfile p' fallback z.2.1 z.1) =
      fun z => μ.weight (e z).2 * rightCommonProfile p fallback (e z).2.2 (e z).1 := rfl
  rw [hc, hd] at h
  change totalVariation (fun z => p (e z)) _ ≤
    totalVariation (fun z => p (e z)) _ + _ at h
  rw [totalVariation_comp_equiv e p (rightRevealModel μ p)] at h
  rw [totalVariation_comp_equiv e p
    (fun z => μ.weight z.2 * rightCommonProfile p fallback z.2.2 z.1)] at h
  have hm : totalVariation (secondMarginal p') μ'.weight =
      totalVariation (secondMarginal p) μ.weight := by
    change totalVariation (fun yx => secondMarginal p ((Equiv.prodComm Y X) yx))
      (fun yx => μ.weight ((Equiv.prodComm Y X) yx)) = _
    exact totalVariation_comp_equiv (Equiv.prodComm Y X) _ _
  rw [hm] at h
  exact h

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_SelectedCommonMarginalLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OccurrenceGame.toGame_success _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.restrict_extend _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.success_restrict _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.wins_restrict _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.PerfectCompleteness.SourceGame.questionGame_success _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The common-data law has exactly the actual selected-event question marginal.
Removing the fair endpoint reveal and regrouping the outside data preserve
the embedded question pair. -/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games Information
noncomputable section

variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem partialRevealMarginal_secondMarginal
    (μ : FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    secondMarginal (partialRevealMarginal μ j likelihood) =
      secondMarginal (fullRevealMarginal μ j likelihood) := by
  classical
  funext q
  calc
    _ = ∑ z : (T × ({i : I // i ≠ j} → X ⊕ Y)) × (X ⊕ Y),
        maskedJoint (partialRevealMarginal μ j likelihood) (z,q) := by
      simp [secondMarginal, Fintype.sum_prod_type, maskedJoint]
    _ = _ := by
      apply Fintype.sum_equiv (revealDataSplitEquiv (T := T) j).symm
      intro z
      exact (fullRevealMarginal_merge μ j likelihood z.1.1 z.1.2 z.2 q).symm

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selectedFullReveal_secondMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) :
    secondMarginal (fullRevealMarginal G.questions j
      (selectedOutsideLikelihood G strategy selected)) =
        secondMarginal (selectedRawMarginal G strategy selected j) := by
  classical
  funext q
  apply Fintype.sum_equiv
    (selectedObservationDataEquiv (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected).symm
  intro z
  exact (selectedRawMarginal_fullReveal G strategy selected j (z,q)).symm

theorem selectedRawMarginal_secondMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    secondMarginal (selectedRawMarginal G strategy selected j) =
      (selectedQuestionMarginal G strategy selected positive j.1).weight := by
  classical
  funext q
  calc
    _ = (selectedJointLaw G strategy selected positive).probability
        (fun z => decide (z.2 j = q)) := by
      simp only [secondMarginal, selectedRawMarginal, FiniteDistribution.probability,
        selectedJointLaw, toGameLaw, Fintype.sum_prod_type, decide_eq_true_eq]
    _ = ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
        (fun questions => decide ((questions.1 j.1,questions.2 j.1) = q)) := by
      have h := selectedJointLaw_question_probability G strategy selected positive
        (fun questions => decide ((questions.1 j.1,questions.2 j.1) = q))
      simpa [selectedQuestionTuple, mergeCoordinates, j.property] using h
    _ = _ := by
      rw [FiniteDistribution.weight_eq_probability_singleton, selectedQuestionMarginal,
        FiniteDistribution.probability_pushforward]

/-- The exact marginal identification needed to use the conditioned-question
information bound in the two local common-data profile errors. -/
theorem selectedCommonLaw_secondMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    secondMarginal (selectedCommonLaw G strategy selected positive j).weight =
      (selectedQuestionMarginal G strategy selected positive j.1).weight := by
  change secondMarginal (partialRevealMarginal G.questions j
    (selectedOutsideLikelihood G strategy selected)) = _
  rw [partialRevealMarginal_secondMarginal, selectedFullReveal_secondMarginal]
  exact selectedRawMarginal_secondMarginal G strategy selected positive j

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_CompletedSamplingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The two actual conditional common-data profiles used by the shared
sampler, with explicit normalized default laws on all null inputs. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selectedRightProfileError_le (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    selectedRightProfileError G strategy selected positive j ≤
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (rightRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))) +
      totalVariation (secondMarginal (selectedCommonLaw G strategy selected positive j).weight)
        G.questions.weight :=
  rightCommonProfile_error _ G.questions _
    (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
    (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j))

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedQuestionRadius_le_informationRadius [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
      Real.log (1 / G.selectedSuccess strategy selected)) ≤
      selectedInformationRadius G strategy selected := by
  have hcard : (1 : ℝ) ≤ Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) := by
    exact_mod_cast (Nat.succ_le_of_lt
      (Fintype.card_pos : 0 < Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)))
  have hlog := Real.log_nonneg hcard
  have hnonneg : 0 ≤ (Fintype.card {i : Fin n // i ∉ selected} : ℝ) := Nat.cast_nonneg _
  unfold selectedInformationRadius
  apply Real.sqrt_le_sqrt
  nlinarith

theorem selectedQuestionMarginal_error_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected},
      (selectedQuestionMarginal G strategy selected positive j.1).totalVariation G.questions) ≤
      selectedInformationRadius G strategy selected :=
  (unselectedQuestionMarginal_totalVariation_sum_le_sqrt G strategy selected positive).trans
    (selectedQuestionRadius_le_informationRadius G strategy selected)

theorem selectedRightProfileError_sum_oai [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, selectedRightProfileError G strategy selected positive j) ≤
      3 * selectedInformationRadius G strategy selected := by
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset {i : Fin n // i ∉ selected})) =>
      selectedRightProfileError_le G strategy selected positive j)
  simp_rw [selectedCommonLaw_secondMarginal] at hsum
  rw [Finset.sum_add_distrib] at hsum
  have hright := selected_rightReveal_error_sum G strategy selected positive
  have hquestion := selectedQuestionMarginal_error_sum G strategy selected positive
  change (∑ j : {i : Fin n // i ∉ selected},
    Information.totalVariation (selectedQuestionMarginal G strategy selected positive j.1).weight
      G.questions.weight) ≤ _ at hquestion
  linarith

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.UniqueGamesTheorem.Foundations.Repetition.selectedRightProfileError_sum_oai.{u_1, u_2, u_3, u_4} := @OAI.UniqueGamesTheorem.Foundations.Repetition.selectedRightProfileError_sum_oai.{u_1, u_2, u_3, u_4}
