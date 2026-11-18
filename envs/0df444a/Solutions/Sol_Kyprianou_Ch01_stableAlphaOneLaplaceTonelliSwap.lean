-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneLaplaceTonelliSwap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T09:25:16.401909+00:00
-- url     : https://prove2.me/submissions/be6d0fdd-ae6f-49c6-9ffe-f5c80754808f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Real Set
open scoped ENNReal
set_option autoImplicit false
/-! Tonelli equality for the nonnegative Laplace-cosine kernel. -/
theorem solution :
    (∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ a in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (a * Real.exp (-(a * x)) * (1 - Real.cos x))) =
    ∫⁻ a in Set.Ioi (0 : ℝ), ∫⁻ x in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (a * Real.exp (-(a * x)) * (1 - Real.cos x)) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (p.2 * Real.exp (-(p.2 * p.1)) *
        (1 - Real.cos p.1))) := by
    fun_prop
  exact MeasureTheory.lintegral_lintegral_swap
    (μ := μ) (ν := μ) (f := fun x a =>
      ENNReal.ofReal (a * Real.exp (-(a * x)) * (1 - Real.cos x)))
    hmeas.aemeasurable
