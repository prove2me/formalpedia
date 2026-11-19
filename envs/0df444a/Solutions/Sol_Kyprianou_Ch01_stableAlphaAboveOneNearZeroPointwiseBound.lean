-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneNearZeroPointwiseBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:19:32.47834+00:00
-- url     : https://prove2.me/submissions/23e64319-39ef-4375-b4ec-4c0fb078a4b9

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Quadratic near-zero bound on the compensated Fourier kernel. -/
theorem solution (alpha r : ℝ) (hr : 0 < r) (hsmall : r ≤ 1) :
    ‖(Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) /
          (((r ^ (alpha + 1) : ℝ)) : ℂ)‖ ≤
      r ^ (1 - alpha) := by
  have hden : 0 ≤ r ^ (alpha + 1) :=
    (Real.rpow_pos_of_pos hr _).le
  have hnorm_den :
      ‖(((r ^ (alpha + 1) : ℝ)) : ℂ)‖ =
        r ^ (alpha + 1) := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hden]
  have hnorm_i : ‖Complex.I * (r : ℂ)‖ = r := by
    simp [norm_mul, Complex.norm_I, Complex.norm_real, abs_of_pos hr]
  have htaylor := Complex.norm_exp_sub_one_sub_id_le
    (show ‖Complex.I * (r : ℂ)‖ ≤ 1 by
      rw [hnorm_i]; exact hsmall)
  rw [hnorm_i] at htaylor
  calc
    ‖(Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) /
          (((r ^ (alpha + 1) : ℝ)) : ℂ)‖ =
        ‖Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)‖ / r ^ (alpha + 1) := by
            rw [norm_div, hnorm_den]
    _ ≤ r ^ (2 : ℕ) / r ^ (alpha + 1) :=
      div_le_div_of_nonneg_right htaylor hden
    _ = r ^ (1 - alpha) := by
      rw [← Real.rpow_natCast (x := r) (n := 2),
        ← Real.rpow_sub hr]
      congr 1
      ring
