-- Prove2me | solution 1 for GlobalTheory.enorm_pow_mul_lintegral_ball_le_of_centre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:16:05.033178+00:00
-- url     : https://prove2.me/submissions/5655a319-4582-46ce-8e6d-2e49103b4443

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
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
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure] {a : E}
    {r : ℝ} {φ : E → H} (hφ : DifferentiableOn ℂ φ (ball a r)) {w : ℝ → ℝ≥0∞}
    (hw : Measurable w) (n : ℕ) :
    ‖φ a‖ₑ ^ n * ∫⁻ z in ball a r, w ‖z - a‖ ∂μ ≤
      ∫⁻ z in ball a r, ‖φ z‖ₑ ^ n * w ‖z - a‖ ∂μ := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have hp : (fun z : E => z + a) ⁻¹' ball a r = ball 0 r := by
    ext z; simp
  have hd : DifferentiableOn ℂ (fun z => φ (z + a)) (ball 0 r) :=
    hφ.comp (differentiableOn_id.add_const a) fun z hz => by simpa using hz
  have h := enorm_pow_mul_lintegral_ball_le μ hd hw n
  have hm := measurePreserving_add_right μ a
  have he := (MeasurableEquiv.addRight a).measurableEmbedding
  rw [← hm.setLIntegral_comp_preimage_emb he _ (ball a r),
    ← hm.setLIntegral_comp_preimage_emb he _ (ball a r), hp]
  simpa using h
end GlobalTheory
