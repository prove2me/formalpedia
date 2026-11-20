-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaBelowOneGammaRecurrence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:28:53.323623+00:00
-- url     : https://prove2.me/submissions/ad82ab96-13c7-4e90-b4c7-46daa85bc7ac

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real Complex MeasureTheory Set
set_option autoImplicit false

/-- Non-pole Gamma recurrence on the stable index interval below one. -/
theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1) :
    Real.Gamma (1 - alpha) = (-alpha) * Real.Gamma (-alpha) := by
  have hne : (-alpha : ℝ) ≠ 0 := by linarith
  convert Real.Gamma_add_one (s := -alpha) hne using 1 <;> ring
