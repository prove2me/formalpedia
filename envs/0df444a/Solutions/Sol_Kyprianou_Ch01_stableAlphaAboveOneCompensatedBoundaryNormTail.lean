-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneCompensatedBoundaryNormTail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:41:43.171368+00:00
-- url     : https://prove2.me/submissions/e03bad83-4355-43d9-ae3f-ca0245f78f96

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false


/-- Linear growth of the compensated Fourier numerator yields vanishing tail power. -/
theorem solution (alpha r : ℝ) (h1 : 1 < alpha) (h2 : alpha < 2)
    (hr : 1 < r) :
    ‖(Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) * (((r ^ (-alpha)) : ℝ) : ℂ)‖ ≤
      2 * r ^ (1 - alpha) := by
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hbound : ‖Complex.exp (Complex.I * (r : ℂ)) - 1 -
      Complex.I * (r : ℂ)‖ ≤ 2 * r := by
    calc
      ‖Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)‖ ≤
          ‖Complex.exp (Complex.I * (r : ℂ)) - 1‖ +
            ‖Complex.I * (r : ℂ)‖ := norm_sub_le _ _
      _ ≤ r + r := by
        have hd := Real.norm_exp_I_mul_ofReal_sub_one_le (x := r)
        rw [show ‖Complex.I * (r : ℂ)‖ = r by
          simp [norm_mul, Complex.norm_I,
            Complex.norm_real, abs_of_pos hrpos]]
        have hrnorm : ‖r‖ = r := Real.norm_eq_abs r |>.trans (abs_of_pos hrpos)
        exact add_le_add (by simpa [hrnorm] using hd) (le_refl _)
      _ = 2 * r := by ring
  have hpow : 0 ≤ r ^ (-alpha) := Real.rpow_nonneg hrpos.le _
  calc
    ‖(Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) * (((r ^ (-alpha)) : ℝ) : ℂ)‖ =
        ‖Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)‖ * r ^ (-alpha) := by
            rw [norm_mul]
            simp [Complex.norm_real, abs_of_nonneg hpow]
    _ ≤ (2 * r) * r ^ (-alpha) :=
      mul_le_mul_of_nonneg_right hbound hpow
    _ = 2 * r ^ (1 - alpha) := by
      calc
        (2 * r) * r ^ (-alpha) =
          2 * (r ^ (1 : ℝ) * r ^ (-alpha)) := by
            rw [Real.rpow_one]
            ring
        _ = 2 * r ^ (1 - alpha) := by
          rw [← Real.rpow_add hrpos]
          congr 1
