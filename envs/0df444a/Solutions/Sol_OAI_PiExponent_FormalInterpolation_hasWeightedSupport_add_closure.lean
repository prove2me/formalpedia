-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.hasWeightedSupport_add_closure
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:43:00.999191+00:00
-- url     : https://prove2.me/submissions/0dc9fc17-afa6-4a1c-99df-c88485558905

import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent.FormalInterpolation

theorem solution {m : ℕ} (v : Fin (m + 1) → ℝ) (B : ℝ)
    (F G : MvPowerSeries (Fin (m + 1)) ℂ)
    (hF : hasWeightedSupport v B F) (hG : hasWeightedSupport v B G) :
    hasWeightedSupport v B (F + G) := by
  intro b hb
  by_cases hFc : MvPowerSeries.coeff (OAI.PiExponent.InterpolationMatrix.exponentVector b) F ≠ 0
  · exact hF b hFc
  · have hFzero : MvPowerSeries.coeff (OAI.PiExponent.InterpolationMatrix.exponentVector b) F = 0 := by
      by_contra h
      exact hFc h
    have hGc : MvPowerSeries.coeff (OAI.PiExponent.InterpolationMatrix.exponentVector b) G ≠ 0 := by
      intro hGzero
      apply hb
      simp [hFzero, hGzero]
    exact hG b hGc