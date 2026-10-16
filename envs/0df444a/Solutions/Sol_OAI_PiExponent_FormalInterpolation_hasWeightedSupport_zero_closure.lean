-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.hasWeightedSupport_zero_closure
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:32:44.514683+00:00
-- url     : https://prove2.me/submissions/bf61f422-df52-498b-b98d-8409cd47e227

import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent.FormalInterpolation

theorem solution {m : ℕ} (v : Fin (m + 1) → ℝ) (B : ℝ) :
    hasWeightedSupport v B (0 : MvPowerSeries (Fin (m + 1)) ℂ) := by
  simp [hasWeightedSupport]