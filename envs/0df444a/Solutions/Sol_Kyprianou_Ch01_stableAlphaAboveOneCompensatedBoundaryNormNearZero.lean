-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneCompensatedBoundaryNormNearZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:41:35.869087+00:00
-- url     : https://prove2.me/submissions/e1267ba6-943b-4ea6-919d-d2e335239f55

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false


/-- Quadratic Taylor remainder yields the exact near-zero boundary power. -/
theorem solution (alpha r : ℝ) (h1 : 1 < alpha) (h2 : alpha < 2)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    ‖(Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) * (((r ^ (-alpha)) : ℝ) : ℂ)‖ ≤
      r ^ (2 - alpha) := by
  have hi : ‖Complex.I * (r : ℂ)‖ = r := by
    simp [norm_mul, Complex.norm_I, Complex.norm_real, abs_of_pos hr]
  have htaylor := Complex.norm_exp_sub_one_sub_id_le
    (show ‖Complex.I * (r : ℂ)‖ ≤ 1 by
      rw [hi]; exact hr1)
  rw [hi] at htaylor
  have hpow : 0 ≤ r ^ (-alpha) := Real.rpow_nonneg hr.le _
  calc
    ‖(Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) * (((r ^ (-alpha)) : ℝ) : ℂ)‖ =
        ‖Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)‖ * r ^ (-alpha) := by
            rw [norm_mul]
            simp [Complex.norm_real, abs_of_nonneg hpow]
    _ ≤ r ^ (2 : ℕ) * r ^ (-alpha) :=
      mul_le_mul_of_nonneg_right htaylor hpow
    _ = r ^ (2 - alpha) := by
      rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr]
      congr 1
