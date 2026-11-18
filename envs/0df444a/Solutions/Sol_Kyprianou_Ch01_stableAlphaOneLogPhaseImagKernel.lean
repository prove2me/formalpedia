-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneLogPhaseImagKernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:35:12.249204+00:00
-- url     : https://prove2.me/submissions/9fdf9b83-1aed-40c9-a124-0c21df715202

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Set Real
set_option autoImplicit false
/-! Imaginary part of the compensated alpha-one stable kernel. -/
theorem solution
    (z r : ℝ) :
    (((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)).im =
      ((z * r) * (if r < 1 then 1 else 0) - Real.sin (z * r)) / r ^ 2 := by
  have hExp :
      (Complex.exp (Complex.I * (((z * r : ℝ) : ℂ)))).im =
        Real.sin (z * r) := by
    rw [mul_comm]
    exact Complex.exp_ofReal_mul_I_im (z * r)
  have hLinear :
      (Complex.I * (((z * r : ℝ) : ℂ)) *
        (if r < 1 then (1 : ℂ) else 0)).im =
          (z * r) * (if r < 1 then 1 else 0 : ℝ) := by
    split_ifs <;> simp [Complex.I_mul_im]
  simp only [Complex.div_ofReal_im, Complex.add_im, Complex.sub_im,
    Complex.one_im, hExp, hLinear, zero_sub]
  ring
