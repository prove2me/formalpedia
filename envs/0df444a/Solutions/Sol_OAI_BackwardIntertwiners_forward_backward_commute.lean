-- Prove2me | solution 1 for OAI.BackwardIntertwiners.forward_backward_commute
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:10:13.660988+00:00
-- url     : https://prove2.me/submissions/706a18d1-130a-412a-90ea-6e9f643246b5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/GlobalOperators.lean:L397-L409
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.forward_backward_commute. The node keeps its source
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
import Theorems.Thm_OAI_BackwardIntertwiners_bilateralWeight_ratio

-- ---- from OAI.Analysis.BackwardIntertwiners.BackwardWeights ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

lemma explicitWeight_ratio (x : Base) (j : ℤ) :
    explicitWeight x (j+1) / explicitWeight x j = explicitBeta x j :=
  bilateralWeight_ratio _ _ _

lemma rawBackward_recurrence (x : Base) (j : ℤ) :
    rawBackward x (j+1)*explicitBeta x j = rawBackward x j*explicitBeta (odometer x) (j-1) := by
  rw [← explicitWeight_ratio x j, ← explicitWeight_ratio (odometer x) (j-1)]
  simp only [rawBackward, add_sub_cancel_right, sub_add_cancel]
  have h₀ := ne_of_gt (explicitWeight_pos x j)
  have h₁ := ne_of_gt (explicitWeight_pos x (j+1))
  have h₂ := ne_of_gt (explicitWeight_pos (odometer x) (j-1))
  field_simp

lemma backwardCoeff_recurrence (x : Base) (j : ℤ) :
    backwardCoeff x (j+1)*explicitBeta x j = backwardCoeff x j*explicitBeta (odometer x) (j-1) := by
  unfold backwardCoeff
  split_ifs with hx
  · simpa only [div_mul_eq_mul_div] using congrArg (fun y => y/backwardBound x) (rawBackward_recurrence x j)
  · simp
end
end BackwardIntertwiners

end OAI

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

lemma backwardFiber_intertwines (x : Base) :
    forwardFiber (odometer x) * backwardFiber x = backwardFiber x * forwardFiber x := by
  ext v j
  simp only [mul_apply_eq_comp, forwardFiber_apply, backwardFiber_apply,
    sub_add_cancel, add_sub_cancel_right]
  have hc := congrArg (fun r : ℝ => (r:ℂ)) (backwardCoeff_recurrence x j)
  push_cast at hc
  linear_combination -hc * v j

lemma forwardOperator_ae (f : GlobalHilbert) :
    forwardOperator f =ᵐ[baseMeasure] fun x => forwardFiber x (f x) :=
  fieldOperator_ae _ _ _ _ _ f
lemma backwardOperator_ae_inverse (f : GlobalHilbert) :
    backwardOperator f =ᵐ[baseMeasure] fun x => backwardFiber (inverseOdometer x) (f (inverseOdometer x)) := by
  have h₁ := Lp.coeFn_compMeasurePreserving (backwardFieldOperator f) inverseOdometer_preserving
  have h₂ := (fieldOperator_ae backwardFiber 1 (by norm_num) backwardFiber_norm_le
    backwardFiber_aestronglyMeasurable f).comp_tendsto inverseOdometer_preserving.quasiMeasurePreserving.tendsto_ae
  exact h₁.trans h₂

lemma forward_backward_commute : forwardOperator * backwardOperator = backwardOperator * forwardOperator := by
  ext1 f
  apply Lp.ext
  filter_upwards [forwardOperator_ae (backwardOperator f), backwardOperator_ae_inverse f,
    backwardOperator_ae_inverse (forwardOperator f),
    (forwardOperator_ae f).comp_tendsto inverseOdometer_preserving.quasiMeasurePreserving.tendsto_ae] with x h₁ h₂ h₃ h₄
  change forwardOperator (backwardOperator f) x = backwardOperator (forwardOperator f) x
  rw [h₁,h₂,h₃]

  dsimp only [Function.comp_def] at h₄
  rw [h₄]
  have hh := congrArg (fun A : Fiber →L[ℂ] Fiber => A (f (inverseOdometer x))) (backwardFiber_intertwines (inverseOdometer x))
  simpa only [mul_apply_eq_comp, odometer_inverseOdometer] using hh

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology
open Topology MeasureTheory Set
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.forward_backward_commute := @_root_.OAI.BackwardIntertwiners.forward_backward_commute
