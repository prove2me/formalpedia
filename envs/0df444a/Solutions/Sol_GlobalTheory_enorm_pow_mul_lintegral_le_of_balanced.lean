-- Prove2me | solution 1 for GlobalTheory.enorm_pow_mul_lintegral_le_of_balanced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:57:32.193457+00:00
-- url     : https://prove2.me/submissions/1d720e60-420c-49d2-bb74-af46475e1461

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Theorems.Thm_GlobalTheory_enorm_pow_mul_lintegral_le_of_circular

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
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure] {S : Set E}
    (hS : MeasurableSet S) (hSc : Balanced ℂ S) {φ : E → H}
    (hφ : ∀ z ∈ S, DifferentiableAt ℂ φ z)
    {w : E → ℝ≥0∞} (hw : Measurable w) (hwc : ∀ c : ℂ, ‖c‖ = 1 → ∀ z ∈ S, w (c • z) = w z)
    (n : ℕ) :
    ‖φ 0‖ₑ ^ n * ∫⁻ z in S, w z ∂μ ≤ ∫⁻ z in S, ‖φ z‖ₑ ^ n * w z ∂μ := by
  refine enorm_pow_mul_lintegral_le_of_circular μ hS (fun c hc z hz => hSc.smul_mem hc.le hz)
    (fun z hz => (hφ z hz).continuousAt.continuousWithinAt) (fun z hz => ?_) hw hwc n
  refine DifferentiableOn.diffContOnCl fun c hc => ?_
  rw [closure_ball _ one_ne_zero, mem_closedBall_zero_iff] at hc
  exact ((hφ _ (hSc.smul_mem hc hz)).comp c
    (differentiableAt_id.smul_const z)).differentiableWithinAt
end GlobalTheory
