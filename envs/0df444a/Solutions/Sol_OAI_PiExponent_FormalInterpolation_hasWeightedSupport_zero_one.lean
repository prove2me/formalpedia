-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.hasWeightedSupport_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:31:20.663569+00:00
-- url     : https://prove2.me/submissions/d587c5e0-4e8d-4004-a330-dfe89c6f2fa1

import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution {m : ℕ} (v : Fin (m + 1) → ℝ) :
    hasWeightedSupport v 0 (1 : MvPowerSeries (Fin (m + 1)) ℂ) := by
  classical
  intro b hb
  have he : OAI.PiExponent.InterpolationMatrix.exponentVector b = 0 := by
    by_contra h
    apply hb
    simp only [MvPowerSeries.coeff_one, if_neg h]
  have hb0 : b = 0 := by
    funext i
    have hbi := congrArg (fun d : Fin (m + 1) →₀ ℕ => d i) he
    change b i = 0 at hbi
    exact hbi
  subst b
  simp