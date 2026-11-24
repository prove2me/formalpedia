-- Prove2me | solution 1 for GlobalTheory.exists_integrableOn_log_norm_of_frequently_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:38:51.916051+00:00
-- url     : https://prove2.me/submissions/1d14336d-a66f-4bc2-a103-5491cbec4706

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableOnOfNormLeSumAbsLogAddLogLog
import Theorems.Thm_GlobalTheory_integrableOn_log_norm_ball

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
    {f : E → ℂ} {x : E} (hf : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ f z) (hx : ∃ᶠ z in 𝓝 x, f z ≠ 0) :
    ∃ r > 0, (∀ᵐ z ∂(μ.restrict (ball x r)), f z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖f z‖) (ball x r) μ := by
  have hb : ∀ᶠ z in 𝓝 x, ‖f z‖ ≤ ‖f x‖ + 1 :=
    (hf.self_of_nhds.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))).mono
      fun _ h => h.le
  obtain ⟨R, hR, hB⟩ := Metric.eventually_nhds_iff_ball.1 (hf.and hb)
  obtain ⟨a, ha, hax⟩ := (hx.and_eventually (ball_mem_nhds x (by positivity : 0 < R / 3))).exists
  have h1 : ball a (2 * R / 3) ⊆ ball x R := ball_subset_ball' (by linarith)
  have h2 : ball x (R / 3) ⊆ ball a (2 * R / 3) :=
    ball_subset_ball' (by rw [dist_comm] at hax; linarith)
  obtain ⟨h3, h4⟩ := integrableOn_log_norm_ball μ (f := f) (a := a) (r := 2 * R / 3)
    (fun z hz => (hB z (h1 hz)).1.differentiableWithinAt) (fun z hz => (hB z (h1 hz)).2) ha
  exact ⟨R / 3, by positivity, ae_restrict_of_ae_restrict_of_subset h2 h3, h4.mono_set h2⟩
end GlobalTheory
