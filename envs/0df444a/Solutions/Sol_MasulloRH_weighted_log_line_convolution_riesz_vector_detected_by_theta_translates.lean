-- Prove2me | solution 1 for MasulloRH.weighted_log_line_convolution_riesz_vector_detected_by_theta_translates
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T05:26:57.489349+00:00
-- url     : https://prove2.me/submissions/30e1d950-bfa6-4666-90f2-e7bc91ea7b0f

import Theorems.Thm_MasulloRH_log_band_weight_convolution_finite_difference_L2
import Theorems.Thm_MasulloRH_rapid_packet_translate_orthogonality_with_L2_differences
import Theorems.Thm_MasulloRH_compact_convolution_rigidity_for_log_band_riesz_weight
import Mathlib
open MeasureTheory
theorem solution
    (α : ℝ) (hα : 0 ≤ α)
    (h u : ℝ → ℂ) (hh : Continuous h) (hhc : HasCompactSupport h)
    (hh0 : h ≠ 0) (hu : Continuous u) (hu0 : u ≠ 0)
    (hdec : ∀ t : ℝ, Integrable (fun x : ℝ => Real.exp (t * |x|) * ‖u x‖)) :
    let w : ℝ → ℝ := fun x : ℝ => Real.exp (2 * α * |x|) * (1 + x^2)^2
    let b : ℝ → ℂ := fun x : ℝ => (w x : ℂ) * ∫ y : ℝ, h y / (w (x-y) : ℂ)
    ∃ c : ℝ, (∫ x : ℝ, b x * (starRingEnd ℂ) (u (x-c))) ≠ 0 := by
  classical
  dsimp only
  by_contra! ho
  obtain ⟨hcont,hbound,hLp⟩ := MasulloRH.log_band_weight_convolution_finite_difference_L2 α hα h hh hhc
  apply hh0
  apply MasulloRH.compact_convolution_rigidity_for_log_band_riesz_weight α hα h hh hhc
  exact MasulloRH.rapid_packet_translate_orthogonality_with_L2_differences _ u hcont hbound hLp hu hu0 hdec ho
