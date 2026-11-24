-- Prove2me | solution 1 for GlobalTheory.enorm_pow_mul_lintegral_ball_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:05:43.639709+00:00
-- url     : https://prove2.me/submissions/29705da5-566b-4df8-a635-c5de3be3e63d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Theorems.Thm_GlobalTheory_enorm_pow_mul_lintegral_le_of_balanced

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
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure] {r : ℝ} {φ : E → H}
    (hφ : DifferentiableOn ℂ φ (ball 0 r)) {w : ℝ → ℝ≥0∞} (hw : Measurable w) (n : ℕ) :
    ‖φ 0‖ₑ ^ n * ∫⁻ z in ball 0 r, w ‖z‖ ∂μ ≤ ∫⁻ z in ball 0 r, ‖φ z‖ₑ ^ n * w ‖z‖ ∂μ :=
  enorm_pow_mul_lintegral_le_of_balanced μ measurableSet_ball balanced_ball_zero
    (fun _ hz => hφ.differentiableAt (isOpen_ball.mem_nhds hz)) (w := fun z => w ‖z‖)
    (hw.comp measurable_norm) (fun c hc z _ => by simp [norm_smul, hc]) n
end GlobalTheory
