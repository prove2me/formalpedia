-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianLaplacePrefactor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:09:06.643237+00:00
-- url     : https://prove2.me/submissions/89784804-ca1b-46f1-8773-6e420708da24

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Positivity
open Real
set_option autoImplicit false

theorem solution
    (s : ℝ) (hs : 0 < s) :
    (s / Real.sqrt (2 * Real.pi)) *
      (Real.sqrt Real.pi / Real.sqrt (s ^ 2 / 2)) = 1 := by
  have hd : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)
  have ha : 0 < Real.sqrt (s ^ 2 / 2) := by positivity
  have hproduct : Real.sqrt (2 * Real.pi) *
      Real.sqrt (s ^ 2 / 2) = s * Real.sqrt Real.pi := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
    have heq : (2 * Real.pi) * (s ^ 2 / 2) =
        s ^ 2 * Real.pi := by ring
    rw [heq, Real.sqrt_mul (sq_nonneg s),
      Real.sqrt_sq_eq_abs, abs_of_pos hs]
  field_simp [ne_of_gt hd, ne_of_gt ha]
  nlinarith [hproduct]
