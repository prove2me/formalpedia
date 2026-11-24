-- Prove2me | solution 1 for GlobalTheory.setIntegral_fderiv_eq_zero_of_lattice_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:38:51.820856+00:00
-- url     : https://prove2.me/submissions/5e47a0aa-77ef-439e-b1d3-eedd490f92e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SetIntegralFderivEqZeroOfLatticePeriodic
import Theorems.Thm_GlobalTheory_setIntegral_comp_add_of_lattice_periodic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open MeasureTheory Module
open scoped Pointwise
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
namespace GlobalTheory
theorem _root_.solution
    (L : Submodule ℤ E) [Countable L] {D : Set E}
    (hD : IsAddFundamentalDomain L D μ) (hm : MeasurableSet D) (hb : Bornology.IsBounded D)
    {F : E → ℂ} (hF1 : ContDiff ℝ 1 F) (hF : ∀ (l : L) z, F (z + l) = F z) (v : E) :
    ∫ z in D, fderiv ℝ F z v ∂μ = 0 := by
  have hcont : Continuous (fderiv ℝ F) := hF1.continuous_fderiv one_ne_zero
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hK : IsCompact (Metric.closedBall (0 : E) (R + ‖v‖)) := isCompact_closedBall _ _
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hfin : μ D < ⊤ := hb.measure_lt_top
  have : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 hfin.ne
  have hint : ∀ G : E → ℂ, Continuous G → Integrable G (μ.restrict D) := fun G hG =>
    (hG.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E) R)).mono_set hR
  have hmem : ∀ z ∈ D, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      z + t • v ∈ Metric.closedBall (0 : E) (R + ‖v‖) := by
    intro z hz t ht
    rw [mem_closedBall_zero_iff]
    have h1 : ‖z‖ ≤ R := mem_closedBall_zero_iff.1 (hR hz)
    have ht' : ‖t‖ < 1 := by simpa using ht
    have h2 : ‖t • v‖ ≤ ‖v‖ := by
      rw [norm_smul]
      nlinarith [norm_nonneg v, norm_nonneg t]
    calc ‖z + t • v‖ ≤ ‖z‖ + ‖t • v‖ := norm_add_le _ _
      _ ≤ R + ‖v‖ := add_le_add h1 h2
  have hderiv : ∀ (z : E) (t : ℝ),
      HasDerivAt (fun s : ℝ => F (z + s • v)) (fderiv ℝ F (z + t • v) v) t := by
    intro z t
    have hd : HasFDerivAt F (fderiv ℝ F (z + t • v)) (z + t • v) :=
      (hF1.differentiable one_ne_zero _).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => z + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add z
    exact hd.comp_hasDerivAt t hl
  have hmeas : ∀ᶠ s in nhds (0 : ℝ), AEStronglyMeasurable (fun z => F (z + s • v)) (μ.restrict D) :=
    Filter.Eventually.of_forall fun s =>
      (hF1.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable
  have hint0 : Integrable (fun z => F (z + (0 : ℝ) • v)) (μ.restrict D) :=
    hint _ (hF1.continuous.comp (continuous_id.add continuous_const))
  have hmeas' : AEStronglyMeasurable (fun z => fderiv ℝ F (z + (0 : ℝ) • v) v) (μ.restrict D) :=
    ((hcont.comp (continuous_id.add continuous_const)).clm_apply continuous_const).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂(μ.restrict D), ∀ s ∈ Metric.ball (0 : ℝ) 1,
      ‖fderiv ℝ F (z + s • v) v‖ ≤ M * ‖v‖ := by
    refine (ae_restrict_iff' hm).2 (Filter.Eventually.of_forall fun z hz s hs => ?_)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hM _ (hmem z hz s hs)) (norm_nonneg _))
  have hdiff : ∀ᵐ z ∂(μ.restrict D), ∀ s ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => F (z + t • v)) (fderiv ℝ F (z + s • v) v) s :=
    Filter.Eventually.of_forall fun z s _ => hderiv z s
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := μ.restrict D)
    (F := fun (s : ℝ) (z : E) => F (z + s • v)) (x₀ := 0) (bound := fun _ => M * ‖v‖)
    (F' := fun (s : ℝ) (z : E) => fderiv ℝ F (z + s • v) v)
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) hmeas hint0 hmeas' hbound (integrable_const _) hdiff
  have hconst : (fun s : ℝ => ∫ z in D, F (z + s • v) ∂μ) = fun _ => ∫ z in D, F z ∂μ :=
    funext fun s => setIntegral_comp_add_of_lattice_periodic μ L hD hF (s • v)
  have h3 : HasDerivAt (fun _ : ℝ => ∫ z in D, F z ∂μ)
      (∫ z in D, fderiv ℝ F (z + (0 : ℝ) • v) v ∂μ) 0 := by
    rw [← hconst]
    exact key.2
  simpa using h3.unique (hasDerivAt_const _ _)
end GlobalTheory
