-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneComplexIntegralNegativeConjugate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:33:34.88835+00:00
-- url     : https://prove2.me/submissions/6844eac9-277c-496a-9882-49f0dd93074f

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneComplexKernelNegativeConjugate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Set Real
set_option autoImplicit false
/-! Integrating the source-conjugate Lévy kernel yields the conjugate exponent integral. -/
theorem solution
    (z : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * ((((-z) * r : ℝ) : ℂ))) +
        Complex.I * ((((-z) * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume) =
      star (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume) := by
  calc
    (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * ((((-z) * r : ℝ) : ℂ))) +
        Complex.I * ((((-z) * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume) =
      ∫ r in Set.Ioi (0 : ℝ), star (((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)) ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with r
        exact Kyprianou.Ch01.stableAlphaOneComplexKernelNegativeConjugate z r
    _ = star (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume) := by
      simpa only [Complex.star_def] using
        (integral_conj (μ := volume.restrict (Set.Ioi (0 : ℝ)))
          (f := fun r : ℝ => ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)))
