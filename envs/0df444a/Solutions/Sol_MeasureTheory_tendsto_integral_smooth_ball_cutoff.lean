-- Prove2me | solution 1 for MeasureTheory.tendsto_integral_smooth_ball_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T10:24:32.443959+00:00
-- url     : https://prove2.me/submissions/d229f2f4-8742-4c31-92e2-b942e411953d

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

def cutoff (x : E) (r ε : ℝ) (y : E) : ℝ :=
  Real.smoothTransition ((r ^ 2 - ‖y - x‖ ^ 2) / ε)

theorem cutoff_contDiff (x : E) (r ε : ℝ) : ContDiff ℝ 1 (cutoff x r ε) := by
  apply Real.smoothTransition.contDiff.comp
  exact (contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)).div_const ε

theorem cutoff_nonneg (x : E) (r ε : ℝ) (y : E) : 0 ≤ cutoff x r ε y :=
  Real.smoothTransition.nonneg _

theorem cutoff_le_one (x : E) (r ε : ℝ) (y : E) : cutoff x r ε y ≤ 1 :=
  Real.smoothTransition.le_one _

theorem cutoff_eq_zero {x : E} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε)
    {y : E} (hy : r ≤ ‖y - x‖) : cutoff x r ε y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ hε.le
  nlinarith [norm_nonneg (y - x)]

theorem cutoff_tsupport_subset {x : E} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    tsupport (cutoff x r ε) ⊆ closedBall x r := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  by_contra h
  simp only [mem_closedBall, dist_eq_norm] at h
  have hy' : r ≤ ‖y - x‖ := by
    exact (not_le.mp h).le
  exact hy (cutoff_eq_zero hr hε hy')

theorem cutoff_eq_one {x : E} {r ε : ℝ} (hε : 0 < ε)
    {y : E} (hy : ε ≤ r ^ 2 - ‖y - x‖ ^ 2) : cutoff x r ε y = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ hε).2 (by simpa)

theorem tendsto_cutoff_integral {x : E} {r : ℝ} (hr : 0 < r)
    {h : E → ℝ} (hh : ContinuousOn h (closedBall x r))
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => ∫ y, cutoff x r (ε k) y * h y ∂μ) atTop
      (𝓝 (∫ y in ball x r, h y ∂μ)) := by
  have hhi : IntegrableOn h (ball x r) μ :=
    (hh.integrableOn_compact (isCompact_closedBall x r)).mono_set ball_subset_closedBall
  have hlim : ∀ y ∈ ball x r,
      Tendsto (fun k => cutoff x r (ε k) y * h y) atTop (𝓝 (h y)) := by
    intro y hy
    have hd : ‖y - x‖ < r := by simpa only [mem_ball, dist_eq_norm] using hy
    have hc : 0 < r ^ 2 - ‖y - x‖ ^ 2 := by nlinarith [norm_nonneg (y - x)]
    have he : ∀ᶠ k in atTop, ε k ≤ r ^ 2 - ‖y - x‖ ^ 2 :=
      (hεlim.eventually (gt_mem_nhds hc)).mono fun _ hk => hk.le
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with k hk
    simp [cutoff_eq_one (hε k) hk]
  have ht := tendsto_integral_of_dominated_convergence
    (μ := μ.restrict (ball x r)) (fun y => ‖h y‖)
    (F := fun k y => cutoff x r (ε k) y * h y)
    (fun k => ((cutoff_contDiff x r (ε k)).continuous.continuousOn.mul
      (hh.mono ball_subset_closedBall)).aestronglyMeasurable measurableSet_ball)
    hhi.norm
    (fun k => (ae_restrict_mem measurableSet_ball).mono fun y _ => by
      rw [norm_mul, Real.norm_of_nonneg (cutoff_nonneg x r (ε k) y)]
      exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one x r (ε k) y))
    ((ae_restrict_mem measurableSet_ball).mono fun y hy => hlim y hy)
  have heq : ∀ k, (∫ y, cutoff x r (ε k) y * h y ∂μ) =
      ∫ y in ball x r, cutoff x r (ε k) y * h y ∂μ := by
    intro k
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hyn
    have hd : r ≤ ‖y - x‖ := by
      simpa only [mem_ball, dist_eq_norm, not_lt] using hyn
    simp [cutoff_eq_zero hr.le (hε k) hd]
  simpa only [heq] using ht


end DirectionalBallWork

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsAddHaarMeasure μ]
    {x : E} {r : ℝ} (hr : 0 < r)
    {h : E → ℝ} (hh : ContinuousOn h (closedBall x r))
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => ∫ y,
      Real.smoothTransition ((r ^ 2 - ‖y - x‖ ^ 2) / ε k) * h y ∂μ)
      atTop (𝓝 (∫ y in ball x r, h y ∂μ)) := by
  exact DirectionalBallWork.tendsto_cutoff_integral hr hh ε hε hεlim
