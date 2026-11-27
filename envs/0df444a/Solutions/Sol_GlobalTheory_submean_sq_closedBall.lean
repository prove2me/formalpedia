-- Prove2me | solution 1 for GlobalTheory.submean_sq_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:41:56.751158+00:00
-- url     : https://prove2.me/submissions/22482250-ca4e-4118-9262-64fb564c03b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Theorems.Thm_GlobalTheory_enorm_pow_mul_lintegral_closedBall_le
import Theorems.Thm_GlobalTheory_volume_closedBall_euclideanSpace_complex

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
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory
theorem _root_.solution {D : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] {r : ℝ} (hr : 0 < r) {φ : EuclideanSpace ℂ (Fin D) → H}
    (hφ : DifferentiableOn ℂ φ (ball 0 r)) :
    (∀ w : ℝ → ℝ≥0∞, Measurable w →
      ‖φ 0‖ₑ ^ 2 * ∫⁻ z in closedBall (0 : EuclideanSpace ℂ (Fin D)) r, w ‖z‖ ≤
        ∫⁻ z in closedBall (0 : EuclideanSpace ℂ (Fin D)) r, ‖φ z‖ₑ ^ 2 * w ‖z‖) ∧
    ‖φ 0‖ₑ ^ 2 ≤ (volume (closedBall (0 : EuclideanSpace ℂ (Fin D)) r))⁻¹ *
      ∫⁻ z in closedBall (0 : EuclideanSpace ℂ (Fin D)) r, ‖φ z‖ₑ ^ 2 ∧
    volume (closedBall (0 : EuclideanSpace ℂ (Fin D)) r) =
      ENNReal.ofReal (π ^ D * r ^ (2 * D) / D.factorial) := by
  refine ⟨fun w hw => enorm_pow_mul_lintegral_closedBall_le volume hφ hw 2, ?_, ?_⟩
  · have h := enorm_pow_mul_lintegral_closedBall_le volume hφ (w := fun _ => 1) measurable_const 2
    simp only [lintegral_const, one_mul, mul_one, MeasurableSet.univ, Measure.restrict_apply,
      univ_inter] at h
    rw [← ENNReal.div_eq_inv_mul,
      ENNReal.le_div_iff_mul_le (Or.inl (measure_closedBall_pos _ _ hr).ne')
        (Or.inl measure_closedBall_lt_top.ne)]
    exact h
  · simpa using volume_closedBall_euclideanSpace_complex (0 : EuclideanSpace ℂ (Fin D)) hr
end GlobalTheory
