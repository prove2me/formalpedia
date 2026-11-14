-- Prove2me | solution 1 for KSATSingleFlip.Connect.exponential_convolution_moment
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:51:28.468375+00:00
-- url     : https://prove2.me/submissions/3116c03a-094b-4fd2-9aa1-0b523a5a3766

import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

theorem solution (μ ν : Measure ℝ) [SFinite ν] (c : ℝ) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (c*z)) ∂(μ ∗ ν)) =
      (∫⁻ x, ENNReal.ofReal (Real.exp (c*x)) ∂μ) *
      (∫⁻ y, ENNReal.ofReal (Real.exp (c*y)) ∂ν) := by
  have hf : Measurable (fun z : ℝ => ENNReal.ofReal (Real.exp (c*z))) := by fun_prop
  rw [Measure.lintegral_conv hf]
  have he (x y : ℝ) : ENNReal.ofReal (Real.exp (c*(x+y))) =
      ENNReal.ofReal (Real.exp (c*x))*ENNReal.ofReal (Real.exp (c*y)) := by
    rw [show c*(x+y) = c*x+c*y by ring, Real.exp_add, ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
  simp_rw [he, lintegral_const_mul _ hf]
  exact lintegral_mul_const _ hf
