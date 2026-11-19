-- Prove2me | solution 1 for LevyStochCalc.Analysis.lipschitz_neg_sq_mul_sin_scaled
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T03:07:14.859589+00:00
-- url     : https://prove2.me/submissions/c7722040-7e46-4170-8013-7220111a7762

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Real

theorem solution (l u v : ℝ) :
    |-l ^ 2 * Real.sin (l * u) - -l ^ 2 * Real.sin (l * v)| ≤ |l| ^ 3 * |u - v| := by
  have h1 : |-l ^ 2 * Real.sin (l * u) - -l ^ 2 * Real.sin (l * v)| =
      l ^ 2 * |Real.sin (l * u) - Real.sin (l * v)| := by
    rw [show -l ^ 2 * Real.sin (l * u) - -l ^ 2 * Real.sin (l * v) =
      -(l ^ 2) * (Real.sin (l * u) - Real.sin (l * v)) by ring, abs_mul, abs_neg,
      abs_of_nonneg (sq_nonneg l)]
  rw [h1]
  calc l ^ 2 * |Real.sin (l * u) - Real.sin (l * v)|
      ≤ l ^ 2 * |l * u - l * v| :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le _ _) (sq_nonneg l)
    _ = |l| ^ 3 * |u - v| := by
        rw [← mul_sub, abs_mul, ← sq_abs l]
        ring
