-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianLaplaceRootProduct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:16:19.95856+00:00
-- url     : https://prove2.me/submissions/8f01f1a0-95fc-419b-becd-a8ec6ba4ad2e

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
open Real
set_option autoImplicit false

theorem solution
    (s b q : ℝ) (hs : 0 < s) (hq : 0 ≤ q) :
    2 * Real.sqrt ((s ^ 2 / 2) * (b ^ 2 / 2 + q)) =
      s * Real.sqrt (b ^ 2 + 2 * q) := by
  have hc : 0 ≤ b ^ 2 + 2 * q := by positivity
  have ha : 0 ≤ (s ^ 2 / 2) * (b ^ 2 / 2 + q) := by positivity
  have heq : (s ^ 2 / 2) * (b ^ 2 / 2 + q) =
      (s ^ 2) * ((b ^ 2 + 2 * q) / 4) := by ring
  rw [heq, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs,
      abs_of_pos hs]
  have h4 : Real.sqrt ((b ^ 2 + 2 * q) / 4) =
      Real.sqrt (b ^ 2 + 2 * q) / 2 := by
    have hfour : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq_eq_abs]
      norm_num
    rw [Real.sqrt_div hc (4 : ℝ), hfour]
  rw [h4]
  ring
