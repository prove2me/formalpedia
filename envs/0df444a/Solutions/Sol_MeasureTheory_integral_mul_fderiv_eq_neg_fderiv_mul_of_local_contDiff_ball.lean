-- Prove2me | solution 1 for MeasureTheory.integral_mul_fderiv_eq_neg_fderiv_mul_of_local_contDiff_ball
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T10:23:40.139733+00:00
-- url     : https://prove2.me/submissions/519f365c-b92c-4bd8-9756-d7948358e15f

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory MeasureTheory.Measure Set Metric Filter Function
open scoped Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section
namespace DirectionalBallWork

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ]

/-- A cutoff supported in the closed ball needs regularity of `f` only there. -/
theorem local_cutoff_integration_by_parts
    {f g : E → ℝ} {x : E} {r : ℝ}
    (hf : ∀ y ∈ closedBall x r, ContDiffAt ℝ 1 f y)
    (hg : ContDiff ℝ 1 g) (hgs : tsupport g ⊆ closedBall x r) (v : E) :
    (∫ y, g y * fderiv ℝ f y v ∂μ) =
      -(∫ y, f y * fderiv ℝ g y v ∂μ) := by
  have hfc : ContinuousOn f (closedBall x r) := fun y hy =>
    (hf y hy).continuousAt.continuousWithinAt
  have hfd : ContinuousOn (fun y => fderiv ℝ f y v) (closedBall x r) := by
    have h : ContinuousOn (fderiv ℝ f) (closedBall x r) := fun y hy =>
      ((hf y hy).continuousAt_fderiv (by norm_num)).continuousWithinAt
    exact h.clm_apply continuousOn_const
  have hgd : Continuous (fun y => fderiv ℝ g y v) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hds : support (fun y => fderiv ℝ g y v) ⊆ closedBall x r :=
    (subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ v).trans hgs)
  have int_of_support : ∀ h : E → ℝ,
      ContinuousOn h (closedBall x r) → support h ⊆ closedBall x r → Integrable h μ := by
    intro h hc hs
    rw [← integrableOn_iff_integrable_of_support_subset hs]
    exact hc.integrableOn_compact (isCompact_closedBall x r)
  have hi1 : Integrable (fun y => fderiv ℝ g y v * f y) μ := by
    apply int_of_support _ (hgd.continuousOn.mul hfc)
    exact (support_mul_subset_left _ _).trans hds
  have hi2 : Integrable (fun y => g y * fderiv ℝ f y v) μ := by
    apply int_of_support _ (hg.continuous.continuousOn.mul hfd)
    exact (support_mul_subset_left _ _).trans ((subset_tsupport _).trans hgs)
  have hi3 : Integrable (fun y => g y * f y) μ := by
    apply int_of_support _ (hg.continuous.continuousOn.mul hfc)
    exact (support_mul_subset_left _ _).trans ((subset_tsupport _).trans hgs)
  convert integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi1 hi2 hi3
    (fun y _ => hg.differentiable (by norm_num) y)
    (fun y hy => (hf y (hgs hy)).differentiableAt (by norm_num)) using 1
  congr 1
  apply integral_congr_ae
  exact .of_forall fun _ => mul_comm _ _


end DirectionalBallWork

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsAddHaarMeasure μ]
    {f g : E → ℝ} {x : E} {r : ℝ}
    (hf : ∀ y ∈ closedBall x r, ContDiffAt ℝ 1 f y)
    (hg : ContDiff ℝ 1 g) (hgs : tsupport g ⊆ closedBall x r) (v : E) :
    (∫ y, g y * fderiv ℝ f y v ∂μ) = -(∫ y, f y * fderiv ℝ g y v ∂μ) := by
  exact DirectionalBallWork.local_cutoff_integration_by_parts hf hg hgs v
