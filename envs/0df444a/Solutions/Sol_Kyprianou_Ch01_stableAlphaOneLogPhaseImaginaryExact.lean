-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneLogPhaseImaginaryExact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:56:30.611484+00:00
-- url     : https://prove2.me/submissions/ad5d66b5-09e8-439d-81e2-6f85fae82a65

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseImaginaryScaling
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real Complex
set_option autoImplicit false

theorem solution :
    ∃ k : ℝ, ∀ z : ℝ, 0 < z →
    (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume).im =
      z * Real.log z - k * z := by
  let j : ℝ := (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * ((((1 : ℝ) * r : ℝ) : ℂ))) +
        Complex.I * ((((1 : ℝ) * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume).im
  refine ⟨-j, ?_⟩
  intro z hz
  have h := Kyprianou.Ch01.stableAlphaOneLogPhaseImaginaryScaling z hz
  change (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume).im = z * (j + Real.log z) at h
  rw [h]
  ring
