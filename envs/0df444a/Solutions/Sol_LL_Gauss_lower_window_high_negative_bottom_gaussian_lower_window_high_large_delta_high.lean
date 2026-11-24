-- Prove2me | solution 1 for LL_Gauss_lower_window_high.negative_bottom_gaussian_lower_window_high_large_delta_high
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T00:27:30.386842+00:00
-- url     : https://prove2.me/submissions/cccd66e9-0306-441f-affd-0fdcad9a4a49

import Mathlib.Analysis.MellinTransform
import Definitions.Def_LL_Gauss_lower_window_high_e
import Definitions.Def_LL_Gauss_lower_window_high_gaussianMellin
import Theorems.Thm_GaussianMellinBound_large_delta

open Real LL_Gauss_lower_window_high

theorem solution (δ : ℝ) (hδ : 1 ≤ |δ|)
    {t : ℝ} (hlo : -(21 / 16) ≤ t) (hhi : t ≤ -(5 / 4)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  have h1 : ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
    simpa only [gaussianMellin, e] using
      GaussianMellinBound.large_delta δ hδ (by linarith : -(23 / 16) ≤ t) (by linarith : t ≤ -1)
  linarith [norm_nonneg (gaussianMellin δ ((1 / 2 : ℂ) - Complex.I))]
