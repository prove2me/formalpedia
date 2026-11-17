-- Prove2me | solution 1 for OAI.SharpPlanar.realSpectral_norm
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-16T15:15:52.891211+00:00
-- url     : https://prove2.me/submissions/ff3a1179-284e-4320-80e6-485c834d8fe4

import Mathlib

theorem solution (ell : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (s : ℝ) :
    ‖(Complex.I * Real.pi * (t : ℂ)) ^ ell * Complex.exp (Complex.I * Real.pi * (t : ℂ) * s)‖ ≤
      Real.pi ^ ell := by
  rw [norm_mul, norm_pow, Complex.norm_exp]
  have hre : (Complex.I * Real.pi * (t : ℂ) * s).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero, mul_one]
  have hnorm : ‖Complex.I * Real.pi * (t : ℂ)‖ = Real.pi * t := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_nonneg ht.1]
  rw [hnorm]
  have hle : Real.pi * t ≤ Real.pi := by
    nlinarith [ht.1, ht.2, Real.pi_pos]
  exact pow_le_pow_left₀ (mul_nonneg Real.pi_pos.le ht.1) hle ell
