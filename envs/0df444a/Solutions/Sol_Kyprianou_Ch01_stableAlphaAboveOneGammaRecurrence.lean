-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneGammaRecurrence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:22:52.957281+00:00
-- url     : https://prove2.me/submissions/c5d94c24-1831-4534-974f-d2fd7015ec66

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real Complex
set_option autoImplicit false

/-- Gamma recurrence in the noninteger stable range above one. -/
theorem solution (alpha : ℝ) (h1 : 1 < alpha) (h2 : alpha < 2) :
    Real.Gamma (1 - alpha) = -alpha * Real.Gamma (-alpha) := by
  have hne : (-alpha : ℝ) ≠ 0 := by linarith
  convert Real.Gamma_add_one (s := -alpha) hne using 1 <;> ring
