-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianComplexTiltNonzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:39:35.01131+00:00
-- url     : https://prove2.me/submissions/af62ed96-d291-467b-8e29-8e5778259841

import Mathlib
open Complex Real ComplexOrder
set_option autoImplicit false

theorem solution
    (b : ℝ) (hb : 0 < b) (theta : ℝ) :
    (((b ^ 2 / 2 : ℝ) : ℂ) - Complex.I * (theta : ℂ)) ≠ 0 := by
  intro hz
  have hr : ((((b ^ 2 / 2 : ℝ) : ℂ) -
      Complex.I * (theta : ℂ))).re = 0 := by rw [hz]; rfl
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, sub_zero] at hr
  nlinarith [sq_pos_of_pos hb]
