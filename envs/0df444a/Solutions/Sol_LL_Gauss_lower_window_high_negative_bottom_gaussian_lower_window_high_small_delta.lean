-- Prove2me | solution 1 for LL_Gauss_lower_window_high.negative_bottom_gaussian_lower_window_high_small_delta
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T03:41:41.034801+00:00
-- url     : https://prove2.me/submissions/30ae8475-af01-4bcd-ac00-a7e0f362f90d

import Mathlib.Analysis.MellinTransform
import Definitions.Def_LL_Gauss_lower_window_high_e
import Definitions.Def_LL_Gauss_lower_window_high_gaussianMellin
import Theorems.Thm_GaussianMellinBound_small_delta

open Real LL_Gauss_lower_window_high

theorem solution (δ : ℝ) (hδ : |δ| ≤ 1)
    {t : ℝ} (hlo : -(11 / 8) ≤ t) (hhi : t ≤ -(5 / 4)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  have h1 : ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
    simpa only [gaussianMellin, e] using
      GaussianMellinBound.small_delta δ hδ (by linarith : -(23 / 16) ≤ t) (by linarith : t ≤ -1)
  linarith [norm_nonneg (gaussianMellin δ ((1 / 2 : ℂ) - Complex.I))]
