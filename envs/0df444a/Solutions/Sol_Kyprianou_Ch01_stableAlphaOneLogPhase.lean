-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneLogPhase
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:36:50.267321+00:00
-- url     : https://prove2.me/submissions/14a1aa58-affc-4ecc-9950-b409eab85674

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseIntegrableExact
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseImaginaryExact
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseRealIntegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution :
    ∃ k : ℝ, ∀ z : ℝ, 0 < z →
      IntegrableOn
        (fun r : ℝ =>
          ((1 : ℂ) -
              Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
            Complex.I * (((z * r : ℝ) : ℂ)) *
              (if r < 1 then (1 : ℂ) else 0)) /
            ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ))
        (Set.Ioi (0 : ℝ)) ∧
      (∫ r in Set.Ioi (0 : ℝ),
        ((1 : ℂ) -
            Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
          Complex.I * (((z * r : ℝ) : ℂ)) *
            (if r < 1 then (1 : ℂ) else 0)) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)
          ∂volume) =
        (((Real.pi * z / 2 : ℝ) : ℂ)) +
          Complex.I * (((z * Real.log z : ℝ) : ℂ)) -
          Complex.I * (((k * z : ℝ) : ℂ)) := by
  obtain ⟨k, hImag⟩ :=
    Kyprianou.Ch01.stableAlphaOneLogPhaseImaginaryExact
  refine ⟨k, ?_⟩
  intro z hz
  have hInt := Kyprianou.Ch01.stableAlphaOneLogPhaseIntegrableExact z hz
  refine ⟨hInt, ?_⟩
  apply Complex.ext
  · have hReal :=
      Kyprianou.Ch01.stableAlphaOneLogPhaseRealIntegral z hz hInt
    simpa [Complex.add_re, Complex.sub_re, Complex.I_mul_re] using hReal
  · have hI := hImag z hz
    simpa [Complex.add_im, Complex.sub_im, Complex.I_mul_im] using hI
