-- Prove2me | solution 1 for LevyStochCalc.Analysis.lipschitz_neg_sq_mul_cos_scaled
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T03:07:15.55801+00:00
-- url     : https://prove2.me/submissions/f79cbf2d-ef23-42f9-9dc9-bf3787dbc6b1

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Real

theorem solution (l u v : ℝ) :
    |-l ^ 2 * Real.cos (l * u) - -l ^ 2 * Real.cos (l * v)| ≤ |l| ^ 3 * |u - v| := by
  have h1 : |-l ^ 2 * Real.cos (l * u) - -l ^ 2 * Real.cos (l * v)| =
      l ^ 2 * |Real.cos (l * u) - Real.cos (l * v)| := by
    rw [show -l ^ 2 * Real.cos (l * u) - -l ^ 2 * Real.cos (l * v) =
      -(l ^ 2) * (Real.cos (l * u) - Real.cos (l * v)) by ring, abs_mul, abs_neg,
      abs_of_nonneg (sq_nonneg l)]
  rw [h1]
  calc l ^ 2 * |Real.cos (l * u) - Real.cos (l * v)|
      ≤ l ^ 2 * |l * u - l * v| :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le _ _) (sq_nonneg l)
    _ = |l| ^ 3 * |u - v| := by
        rw [← mul_sub, abs_mul, ← sq_abs l]
        ring
