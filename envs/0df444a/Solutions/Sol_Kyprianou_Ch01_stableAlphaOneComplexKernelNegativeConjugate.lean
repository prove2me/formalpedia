-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneComplexKernelNegativeConjugate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:30:52.016889+00:00
-- url     : https://prove2.me/submissions/db1f2954-c514-4187-86c5-08e853b647fc

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseRealKernel
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseImagKernel
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneImaginaryKernelOdd
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Set Real
set_option autoImplicit false
/-! The full alpha-one compensated complex kernel transforms by conjugation under frequency reversal. -/
theorem solution
    (z r : ℝ) :
    ((1 : ℂ) - Complex.exp (Complex.I * ((((-z) * r : ℝ) : ℂ))) +
        Complex.I * ((((-z) * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) =
      star (((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)) := by
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]
    rw [Kyprianou.Ch01.stableAlphaOneLogPhaseRealKernel (-z) r,
      Kyprianou.Ch01.stableAlphaOneLogPhaseRealKernel z r]
    simp [neg_mul, Real.cos_neg]
  · simp only [Complex.star_def, Complex.conj_im]
    rw [Kyprianou.Ch01.stableAlphaOneLogPhaseImagKernel (-z) r,
      Kyprianou.Ch01.stableAlphaOneLogPhaseImagKernel z r]
    exact Kyprianou.Ch01.stableAlphaOneImaginaryKernelOdd z r
