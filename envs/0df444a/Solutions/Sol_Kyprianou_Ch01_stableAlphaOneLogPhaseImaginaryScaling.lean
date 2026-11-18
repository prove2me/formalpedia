-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneLogPhaseImaginaryScaling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:32:04.192102+00:00
-- url     : https://prove2.me/submissions/e36b25d4-068d-4de9-b432-45160db4d18a

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseIntegrableExact
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneImaginaryIntegralAsSine
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneImaginaryFrequencySubstitution
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneShiftedSineIntegralLogCorrection
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real Complex
set_option autoImplicit false

theorem solution :
    ∀ z : ℝ, 0 < z →
    (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume).im =
      z * ((∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * ((((1 : ℝ) * r : ℝ) : ℂ))) +
        Complex.I * ((((1 : ℝ) * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume).im + Real.log z) := by
  intro z hz
  let J : ℝ → ℂ := fun a =>
    ∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * (((a * r : ℝ) : ℂ))) +
          Complex.I * (((a * r : ℝ) : ℂ)) *
            (if r < 1 then (1 : ℂ) else 0)) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume
  have hzInt := Kyprianou.Ch01.stableAlphaOneLogPhaseIntegrableExact z hz
  have hOneInt := Kyprianou.Ch01.stableAlphaOneLogPhaseIntegrableExact 1
    (by norm_num : (0 : ℝ) < 1)
  have hImagZ : (J z).im =
      ∫ r in Set.Ioi (0 : ℝ), (((z * r) * (if r < 1 then (1 : ℝ) else 0) - Real.sin (z * r)) / r ^ 2) ∂volume := by
    exact Kyprianou.Ch01.stableAlphaOneImaginaryIntegralAsSine z hzInt
  have hImagOne :
      (∫ u in Set.Ioi (0 : ℝ), ((u * (if u < 1 then (1 : ℝ) else 0) - Real.sin u) / u ^ 2) ∂volume) =
        (J 1).im := by
    have h := Kyprianou.Ch01.stableAlphaOneImaginaryIntegralAsSine 1 hOneInt
    simpa only [one_mul, J] using h.symm
  have hScale := Kyprianou.Ch01.stableAlphaOneImaginaryFrequencySubstitution z hz
  have hLog := Kyprianou.Ch01.stableAlphaOneShiftedSineIntegralLogCorrection z hz
  change (J z).im = z * ((J 1).im + Real.log z)
  calc
    (J z).im = ∫ r in Set.Ioi (0 : ℝ), (((z * r) * (if r < 1 then (1 : ℝ) else 0) - Real.sin (z * r)) / r ^ 2) ∂volume := hImagZ
    _ = z * (∫ u in Set.Ioi (0 : ℝ), ((u * (if u < z then (1 : ℝ) else 0) - Real.sin u) / u ^ 2) ∂volume) := hScale
    _ = z * ((∫ u in Set.Ioi (0 : ℝ), ((u * (if u < 1 then (1 : ℝ) else 0) - Real.sin u) / u ^ 2) ∂volume) + Real.log z) := by
      rw [hLog]
    _ = z * ((J 1).im + Real.log z) := by rw [hImagOne]
