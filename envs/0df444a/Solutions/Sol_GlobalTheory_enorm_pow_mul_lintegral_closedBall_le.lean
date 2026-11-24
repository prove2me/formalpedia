-- Prove2me | solution 1 for GlobalTheory.enorm_pow_mul_lintegral_closedBall_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:16:08.527405+00:00
-- url     : https://prove2.me/submissions/5606e863-0016-4ead-81b5-95457c1883e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Theorems.Thm_GlobalTheory_enorm_pow_mul_lintegral_le_of_balanced
import Theorems.Thm_GlobalTheory_enorm_pow_mul_lintegral_ball_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set
open scoped ENNReal Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
namespace GlobalTheory
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure] {r : ℝ}
    {φ : E → H} (hφ : DifferentiableOn ℂ φ (ball 0 r)) {w : ℝ → ℝ≥0∞} (hw : Measurable w) (n : ℕ) :
    ‖φ 0‖ₑ ^ n * ∫⁻ z in closedBall 0 r, w ‖z‖ ∂μ ≤
      ∫⁻ z in closedBall 0 r, ‖φ z‖ₑ ^ n * w ‖z‖ ∂μ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact enorm_pow_mul_lintegral_le_of_balanced μ measurableSet_closedBall
      balanced_closedBall_zero (fun z _ => differentiable_of_subsingleton z) (w := fun z => w ‖z‖)
      (hw.comp measurable_norm) (fun c hc z _ => by simp [norm_smul, hc]) n
  · have h : (closedBall (0 : E) r : Set E) =ᵐ[μ] (ball 0 r : Set E) := by
      rw [← ball_union_sphere]
      exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.2 (μ.addHaar_sphere 0 r))
    rw [Measure.restrict_congr_set h]
    exact enorm_pow_mul_lintegral_ball_le μ hφ hw n
end GlobalTheory
