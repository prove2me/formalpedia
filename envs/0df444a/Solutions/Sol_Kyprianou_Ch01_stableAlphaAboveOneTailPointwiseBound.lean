-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneTailPointwiseBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:28:44.00656+00:00
-- url     : https://prove2.me/submissions/f24c255c-92bc-457d-9df0-93b948a89f86

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Linear far-tail bound on the compensated Fourier kernel. -/
theorem solution (alpha r : ℝ) (hr : 1 < r) :
    ‖(Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) /
          (((r ^ (alpha + 1) : ℝ)) : ℂ)‖ ≤
      2 * r ^ (-alpha) := by
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hden : 0 ≤ r ^ (alpha + 1) :=
    (Real.rpow_pos_of_pos hrpos _).le
  have hnorm_den :
      ‖(((r ^ (alpha + 1) : ℝ)) : ℂ)‖ =
        r ^ (alpha + 1) := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hden]
  have hrem : ‖Complex.exp (Complex.I * (r : ℂ)) - 1 -
      Complex.I * (r : ℂ)‖ ≤ 2 * r := by
    calc
      ‖Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)‖ ≤
          ‖Complex.exp (Complex.I * (r : ℂ)) - 1‖ +
            ‖Complex.I * (r : ℂ)‖ := norm_sub_le _ _
      _ ≤ r + r := by
        simpa [norm_mul, Complex.norm_I,
          Complex.norm_real, abs_of_pos hrpos] using
          (add_le_add
            (by simpa [Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos hrpos] using
                (Real.norm_exp_I_mul_ofReal_sub_one_le (x := r)))
            (le_refl r))
      _ = 2 * r := by ring
  calc
    ‖(Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) /
          (((r ^ (alpha + 1) : ℝ)) : ℂ)‖ =
        ‖Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)‖ / r ^ (alpha + 1) := by
            rw [norm_div, hnorm_den]
    _ ≤ (2 * r) / r ^ (alpha + 1) :=
      div_le_div_of_nonneg_right hrem hden
    _ = 2 * (r / r ^ (alpha + 1)) := by ring
    _ = 2 * r ^ (-alpha) := by
      congr 1
      calc
        r / r ^ (alpha + 1) =
          r ^ ((1 : ℝ) - (alpha + 1)) := by
            rw [Real.rpow_sub hrpos, Real.rpow_one]
        _ = r ^ (-alpha) := by congr 1; ring
