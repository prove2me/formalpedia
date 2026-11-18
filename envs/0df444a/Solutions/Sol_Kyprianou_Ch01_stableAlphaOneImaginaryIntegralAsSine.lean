-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneImaginaryIntegralAsSine
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:14:57.099119+00:00
-- url     : https://prove2.me/submissions/9e865a61-f3f4-4dfc-9ea0-7f8f8ac7f26c

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseImagKernel
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Set Real
set_option autoImplicit false
/-! Imaginary projection of the exact integrable complex Lévy kernel is the sine phase integral. -/
theorem solution
    (z : ℝ)
    (hInt : IntegrableOn
      (fun r : ℝ => ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)) (Set.Ioi (0 : ℝ))) :
    (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume).im =
      ∫ r in Set.Ioi (0 : ℝ),
        ((z * r) * (if r < 1 then (1 : ℝ) else 0) - Real.sin (z * r)) / r ^ 2 ∂volume := by
  have hImag := (integral_im
    (μ := volume.restrict (Set.Ioi (0 : ℝ))) hInt)
  calc
    (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume).im =
      ∫ r in Set.Ioi (0 : ℝ), (((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)).im ∂volume :=
        hImag.symm
    _ = ∫ r in Set.Ioi (0 : ℝ),
          ((z * r) * (if r < 1 then (1 : ℝ) else 0) - Real.sin (z * r)) / r ^ 2 ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with r
        exact Kyprianou.Ch01.stableAlphaOneLogPhaseImagKernel z r
