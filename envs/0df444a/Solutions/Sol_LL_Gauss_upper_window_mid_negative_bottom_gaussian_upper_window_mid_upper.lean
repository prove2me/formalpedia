-- Prove2me | solution 1 for LL_Gauss_upper_window_mid.negative_bottom_gaussian_upper_window_mid_upper
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T03:43:13.487795+00:00
-- url     : https://prove2.me/submissions/9cee616d-24e6-4844-a4ad-c4b3062a1e7f

import Mathlib.Analysis.MellinTransform
import Definitions.Def_LL_Gauss_upper_window_mid_e
import Definitions.Def_LL_Gauss_upper_window_mid_gaussianMellin
import Theorems.Thm_GaussianMellinBound_small_delta
import Theorems.Thm_GaussianMellinBound_large_delta

open Real LL_Gauss_upper_window_mid

theorem solution (δ : ℝ) {t : ℝ}
    (hlo : -(13 / 12) ≤ t) (hhi : t ≤ -(17 / 16)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  have hlo' : -(23 / 16) ≤ t := by linarith
  have hhi' : t ≤ -1 := by linarith
  rcases le_total |δ| 1 with hδ | hδ
  · simpa only [gaussianMellin, e] using GaussianMellinBound.small_delta δ hδ hlo' hhi'
  · simpa only [gaussianMellin, e] using GaussianMellinBound.large_delta δ hδ hlo' hhi'
