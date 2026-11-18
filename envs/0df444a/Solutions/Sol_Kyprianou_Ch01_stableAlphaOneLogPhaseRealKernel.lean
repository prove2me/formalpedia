-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneLogPhaseRealKernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:28:22.506345+00:00
-- url     : https://prove2.me/submissions/ceea1cc3-4947-490c-adf8-d62299615890

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Set Real
set_option autoImplicit false
/-! Real part of the fully compensated index-one complex stable kernel. -/
theorem solution
    (z r : ℝ) :
    (((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)).re =
      (1 - Real.cos (z * r)) / r ^ 2 := by
  have hExp :
      (Complex.exp (Complex.I * (((z * r : ℝ) : ℂ)))).re =
        Real.cos (z * r) := by
    rw [mul_comm]
    exact Complex.exp_ofReal_mul_I_re (z * r)
  have hImag :
      (Complex.I * (((z * r : ℝ) : ℂ)) *
        (if r < 1 then (1 : ℂ) else 0)).re = 0 := by
    split_ifs <;> simp [Complex.I_mul_re]
  simp only [Complex.div_ofReal_re, Complex.add_re,
    Complex.sub_re, Complex.one_re, hExp, hImag, add_zero]
