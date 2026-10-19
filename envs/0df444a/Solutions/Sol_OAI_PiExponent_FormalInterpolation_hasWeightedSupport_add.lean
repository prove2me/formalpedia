-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.hasWeightedSupport_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:50:12.157717+00:00
-- url     : https://prove2.me/submissions/72216c85-06c5-4cc9-aaed-6807267b5958

import Mathlib
import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
theorem solution
    {m : ℕ} (v : Fin (m + 1) → ℝ) (B : ℝ)
    (F G : MvPowerSeries (Fin (m + 1)) ℂ)
    (hF : FormalInterpolation.hasWeightedSupport v B F)
    (hG : FormalInterpolation.hasWeightedSupport v B G) :
    FormalInterpolation.hasWeightedSupport v B (F + G) := by
  intro b hb
  rw [map_add] at hb
  by_cases h : MvPowerSeries.coeff (InterpolationMatrix.exponentVector b) F = 0
  · rw [h, zero_add] at hb; exact hG b hb
  · exact hF b h
