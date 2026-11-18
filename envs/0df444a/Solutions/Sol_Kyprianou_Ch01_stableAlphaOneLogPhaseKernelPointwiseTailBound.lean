-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneLogPhaseKernelPointwiseTailBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:47:42.601783+00:00
-- url     : https://prove2.me/submissions/ca8c4cff-2891-400f-a17b-925f12870764

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real Complex
set_option autoImplicit false
/-! Source-exact bound for the complex compensated alpha-one stable kernel at each positive distance. -/
theorem solution
    (z r : ℝ) (hz : 0 < z) (hrpos : 0 < r) :
    ‖((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)‖ ≤ (2 + z) * r ^ (-2 : ℝ) := by
  have hExp : ‖Complex.exp (Complex.I * (((z * r : ℝ) : ℂ)))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  have hUnit :
      ‖(1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ)))‖ ≤ 2 := calc
    _ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (Complex.I * (((z * r : ℝ) : ℂ)))‖ :=
      norm_sub_le _ _
    _ = 2 := by simp [Complex.norm_exp, Complex.mul_re]; norm_num
  have hLinear :
      ‖Complex.I * (((z * r : ℝ) : ℂ)) *
        (if r < 1 then (1 : ℂ) else 0)‖ ≤ z := by
    by_cases hs : r < 1
    · have hzmul : z * r ≤ z := by
        nlinarith [mul_nonneg hz.le (sub_nonneg.mpr hs.le)]
      have hAbs : |z| * |r| ≤ z := by
        simpa [abs_of_pos hz, abs_of_pos hrpos] using hzmul
      simpa [hs, norm_mul, Complex.norm_I] using hAbs
    · simp [hs, hz.le]
  have hNum : ‖(1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
      Complex.I * (((z * r : ℝ) : ℂ)) *
        (if r < 1 then (1 : ℂ) else 0)‖ ≤ 2 + z := calc
    _ ≤ ‖(1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ)))‖ +
        ‖Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)‖ := norm_add_le _ _
    _ ≤ 2 + z := add_le_add hUnit hLinear
  have hnorm : ‖((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)‖ = r ^ 2 := by
    simp [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
  have hrpow : r ^ (-2 : ℝ) = (r ^ 2)⁻¹ := by
    rw [Real.rpow_neg hrpos.le]
    exact congrArg (fun x : ℝ => x⁻¹) (Real.rpow_natCast r 2)
  change ‖((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
      Complex.I * (((z * r : ℝ) : ℂ)) *
        (if r < 1 then (1 : ℂ) else 0)) / ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)‖ ≤
          (2 + z) * r ^ (-2 : ℝ)
  rw [norm_div, hnorm, hrpow]
  simpa [div_eq_mul_inv] using
    (div_le_div_of_nonneg_right hNum (sq_nonneg r))
