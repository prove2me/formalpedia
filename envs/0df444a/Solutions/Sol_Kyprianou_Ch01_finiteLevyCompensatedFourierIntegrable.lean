-- Prove2me | solution 1 for Kyprianou.Ch01.finiteLevyCompensatedFourierIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:10:37.866065+00:00
-- url     : https://prove2.me/submissions/c36d1a49-4601-489f-9f19-4a94c0b35d32

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex
set_option autoImplicit false
/-! A finite Lévy intensity integrates every bounded compensated Fourier kernel. -/
theorem solution
    (Λ : Measure ℝ) [IsFiniteMeasure Λ] (xi : ℝ) :
    Integrable (fun x : ℝ =>
      Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) Λ := by
  have hmeas : Measurable (fun x : ℝ =>
      Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) := by
    fun_prop
  apply Integrable.of_bound hmeas.aestronglyMeasurable 2
  filter_upwards [] with x
  calc
    ‖Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1‖ ≤
        ‖Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I)‖ +
          ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by
      simp [Complex.norm_exp, Complex.mul_re]
      norm_num
