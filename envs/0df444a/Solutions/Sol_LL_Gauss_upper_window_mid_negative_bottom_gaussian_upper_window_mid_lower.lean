-- Prove2me | solution 1 for LL_Gauss_upper_window_mid.negative_bottom_gaussian_upper_window_mid_lower
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T03:43:02.622833+00:00
-- url     : https://prove2.me/submissions/bb70254f-9a36-4b44-9766-cb7b596f7786

import Mathlib.Analysis.MellinTransform
import Definitions.Def_LL_Gauss_upper_window_mid_e
import Definitions.Def_LL_Gauss_upper_window_mid_gaussianMellin
import Theorems.Thm_GaussianMellinBound_small_delta
import Theorems.Thm_GaussianMellinBound_large_delta

open Real LL_Gauss_upper_window_mid

theorem solution (δ : ℝ) {t : ℝ}
    (hlo : -(9 / 8) ≤ t) (hhi : t ≤ -(53 / 48)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  have hlo' : -(23 / 16) ≤ t := by linarith
  have hhi' : t ≤ -1 := by linarith
  rcases le_total |δ| 1 with hδ | hδ
  · simpa only [gaussianMellin, e] using GaussianMellinBound.small_delta δ hδ hlo' hhi'
  · simpa only [gaussianMellin, e] using GaussianMellinBound.large_delta δ hδ hlo' hhi'
