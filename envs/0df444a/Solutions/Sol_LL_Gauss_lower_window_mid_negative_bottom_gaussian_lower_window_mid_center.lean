-- Prove2me | solution 1 for LL_Gauss_lower_window_mid.negative_bottom_gaussian_lower_window_mid_center
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T03:41:41.031911+00:00
-- url     : https://prove2.me/submissions/adbbc326-addb-4b64-aa4d-8e265985faac

import Mathlib.Analysis.MellinTransform
import Definitions.Def_LL_Gauss_lower_window_mid_e
import Definitions.Def_LL_Gauss_lower_window_mid_gaussianMellin
import Theorems.Thm_GaussianMellinBound_small_delta
import Theorems.Thm_GaussianMellinBound_large_delta

open Real LL_Gauss_lower_window_mid

theorem solution (δ : ℝ) {t : ℝ}
    (hlo : -(17 / 12) ≤ t) (hhi : t ≤ -(67 / 48)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  have hlo' : -(23 / 16) ≤ t := by linarith
  have hhi' : t ≤ -1 := by linarith
  rcases le_total |δ| 1 with hδ | hδ
  · have h1 : ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
        (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
      simpa only [gaussianMellin, e] using GaussianMellinBound.small_delta δ hδ hlo' hhi'
    linarith [norm_nonneg (gaussianMellin δ ((1 / 2 : ℂ) - Complex.I))]
  · have h1 : ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
        (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
      simpa only [gaussianMellin, e] using GaussianMellinBound.large_delta δ hδ hlo' hhi'
    linarith [norm_nonneg (gaussianMellin δ ((1 / 2 : ℂ) - Complex.I))]
