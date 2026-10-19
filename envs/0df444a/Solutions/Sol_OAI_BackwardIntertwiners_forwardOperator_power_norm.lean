-- Prove2me | solution 1 for OAI.BackwardIntertwiners.forwardOperator_power_norm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:13:36.503928+00:00
-- url     : https://prove2.me/submissions/1f2836e4-c540-4613-8b60-5c84d505e67b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/GlobalOperators.lean:L454-L467
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.forwardOperator_power_norm. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ExplicitWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_HaarBase
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberMaps
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_BackwardWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_GlobalOperators
import Theorems.Thm_OAI_BackwardIntertwiners_sum_coordinateDistance_lower

-- ---- from OAI.Analysis.BackwardIntertwiners.GlobalOperators ----
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

section Fields
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma fieldOperator_ae (A : X → Fiber →L[ℂ] Fiber) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ)
    (f : Lp Fiber 2 μ) : fieldOperator A C hC hA hm f =ᵐ[μ] fun x => A x (f x) :=
  fieldVector_ae A C hA hm f

end Fields

lemma explicitExponent_distance (x : Base) (j : ℤ) :
    10*(coordinateDistance j:ℝ) ≤ explicitExponent x j := by
  cases j with
  | ofNat n =>
    have hd : coordinateDistance (n:ℤ) = (n:ℤ)+1 := by
      unfold coordinateDistance
      omega
    change 10*(coordinateDistance (n:ℤ):ℝ) ≤ halfExponent (plusResidue x) n
    rw [hd]
    simpa only [Int.cast_add, Int.cast_one, Int.cast_natCast] using halfExponent_lower (plusResidue x) n
  | negSucc n =>
    have hd : coordinateDistance (Int.negSucc n) = (n:ℤ)+1 := by
      unfold coordinateDistance
      omega
    rw [hd]
    change _ ≤ halfExponent (minusResidue x) n
    simpa only [Int.cast_add, Int.cast_one, Int.cast_natCast] using halfExponent_lower (minusResidue x) n

lemma interval_exponent_lower (x : Base) (n : ℕ) (j : ℤ) :
    10*(powerCost n:ℝ) ≤ ∑ r ∈ Finset.range n, explicitExponent x (j+(r:ℤ)) := by
  have hc : (powerCost n:ℝ) ≤ ∑ r ∈ Finset.range n, (coordinateDistance (j+(r:ℤ)):ℝ) := by
    exact_mod_cast sum_coordinateDistance_lower n j
  calc
    _ ≤ 10*(∑ r ∈ Finset.range n, (coordinateDistance (j+(r:ℤ)):ℝ)) := by linarith
    _ = ∑ r ∈ Finset.range n, 10*(coordinateDistance (j+(r:ℤ)):ℝ) := by rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun _ _ => explicitExponent_distance x _

lemma forwardFiber_power_input (x : Base) (n : ℕ) (v : Fiber) (j : ℤ) :
    (forwardFiber x ^ n) v (j+(n:ℤ)) =
      (Real.exp (-(∑ r ∈ Finset.range n, explicitExponent x (j+(r:ℤ)))):ℂ)*v j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, forwardFiber_apply]
    have hi : j+((n+1:ℕ):ℤ)-1 = j+(n:ℤ) := by omega
    rw [hi, ih, Finset.sum_range_succ]
    change (Real.exp (-explicitExponent x (j+(n:ℤ))):ℂ)*
      ((Real.exp (-(∑ r ∈ Finset.range n, explicitExponent x (j+(r:ℤ)))):ℂ)*v j) = _
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    rw [neg_add_rev]

lemma forwardFiber_power_norm (x : Base) (n : ℕ) :
    ‖forwardFiber x ^ n‖ ≤ Real.exp (-10*(powerCost n:ℝ)) := by
  let C := Real.exp (-10*(powerCost n:ℝ))
  have hC : 0 ≤ C := (Real.exp_pos _).le
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro v
  calc
    _ ≤ ‖(C:ℂ) • fiberReindex (Equiv.subRight (n:ℤ)) v‖ := by
      apply lp.norm_mono (by norm_num : (2:ENNReal) ≠ 0)
      intro j
      have hi : j = (j-(n:ℤ))+(n:ℤ) := by omega
      conv_lhs => rw [hi, forwardFiber_power_input]
      simp only [lp.coeFn_smul, Pi.smul_apply, norm_smul, fiberReindex_apply, Equiv.subRight_apply,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg hC]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      simpa only [neg_mul] using neg_le_neg (interval_exponent_lower x n (j-(n:ℤ)))
    _ = C*‖v‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, (fiberReindex _).norm_map]

lemma forwardOperator_ae (f : GlobalHilbert) :
    forwardOperator f =ᵐ[baseMeasure] fun x => forwardFiber x (f x) :=
  fieldOperator_ae _ _ _ _ _ f
lemma forwardOperator_power_ae (n : ℕ) (f : GlobalHilbert) :
    (forwardOperator^n) f =ᵐ[baseMeasure] fun x => (forwardFiber x ^ n) (f x) := by
  induction n with
  | zero => filter_upwards [] with x; rfl
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    filter_upwards [forwardOperator_ae ((forwardOperator^n) f), ih] with x h₁ h₂
    simp only [h₁,h₂,pow_succ',mul_apply_eq_comp]
lemma forwardOperator_power_norm (n : ℕ) :
    ‖forwardOperator^n‖ ≤ Real.exp (-10*(powerCost n:ℝ)) := by
  let C := Real.exp (-10*(powerCost n:ℝ))
  have hC : 0 ≤ C := (Real.exp_pos _).le
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  calc
    _ ≤ ‖(C:ℂ) • f‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [forwardOperator_power_ae n f, Lp.coeFn_smul (C:ℂ) f] with x h₁ h₂
      rw [h₁,h₂,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg hC]
      exact (forwardFiber x ^ n).le_opNorm (f x) |>.trans
        (mul_le_mul_of_nonneg_right (forwardFiber_power_norm x n) (norm_nonneg _))
    _ = C*‖f‖ := by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hC]

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology
open Topology MeasureTheory Set
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.forwardOperator_power_norm := @_root_.OAI.BackwardIntertwiners.forwardOperator_power_norm
