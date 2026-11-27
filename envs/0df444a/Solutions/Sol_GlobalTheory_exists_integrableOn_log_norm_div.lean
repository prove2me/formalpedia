-- Prove2me | solution 1 for GlobalTheory.exists_integrableOn_log_norm_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:46.944969+00:00
-- url     : https://prove2.me/submissions/134f9a88-3dca-4dde-8d7f-438dad6df539

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableOnOfNormLeSumAbsLogAddLogLog
import Theorems.Thm_GlobalTheory_exists_integrableOn_log_norm_of_frequently_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure]
    {g h : E → ℂ} {x : E} (hg : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ g z)
    (hh : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ h z) (hg0 : ∃ᶠ z in 𝓝 x, g z ≠ 0)
    (hh0 : ∃ᶠ z in 𝓝 x, h z ≠ 0) :
    ∃ r > 0, (∀ᵐ z ∂(μ.restrict (ball x r)), g z ≠ 0 ∧ h z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖g z / h z‖) (ball x r) μ := by
  obtain ⟨r, hr, h1, h2⟩ := exists_integrableOn_log_norm_of_frequently_ne_zero μ hg hg0
  obtain ⟨s, hs, h3, h4⟩ := exists_integrableOn_log_norm_of_frequently_ne_zero μ hh hh0
  have e1 : ball x (min r s) ⊆ ball x r := ball_subset_ball (min_le_left _ _)
  have e2 : ball x (min r s) ⊆ ball x s := ball_subset_ball (min_le_right _ _)
  have h5 := (ae_restrict_of_ae_restrict_of_subset e1 h1).and
    (ae_restrict_of_ae_restrict_of_subset e2 h3)
  refine ⟨min r s, lt_min hr hs, h5, ((h2.mono_set e1).sub (h4.mono_set e2)).congr ?_⟩
  filter_upwards [h5] with z hz
  simp [Real.log_div, hz.1, hz.2]
end GlobalTheory
