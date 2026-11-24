-- Prove2me | solution 1 for LL_Gauss_lower_window_high.negative_bottom_gaussian_lower_window_high_large_delta_low
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T00:25:46.324838+00:00
-- url     : https://prove2.me/submissions/0c0c58ec-5308-4480-a38e-11132544745b

import Mathlib.Analysis.MellinTransform
import Definitions.Def_LL_Gauss_lower_window_high_e
import Definitions.Def_LL_Gauss_lower_window_high_gaussianMellin
import Theorems.Thm_GaussianMellinBound_large_delta

open Real LL_Gauss_lower_window_high

theorem solution (δ : ℝ) (hδ : 1 ≤ |δ|)
    {t : ℝ} (hlo : -(11 / 8) ≤ t) (hhi : t ≤ -(21 / 16)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  have h1 : ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
    simpa only [gaussianMellin, e] using
      GaussianMellinBound.large_delta δ hδ (by linarith : -(23 / 16) ≤ t) (by linarith : t ≤ -1)
  linarith [norm_nonneg (gaussianMellin δ ((1 / 2 : ℂ) - Complex.I))]
