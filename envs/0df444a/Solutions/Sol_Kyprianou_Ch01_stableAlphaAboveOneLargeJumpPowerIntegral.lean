-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneLargeJumpPowerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:36:49.571731+00:00
-- url     : https://prove2.me/submissions/498fd602-7655-4289-b65f-0335bd857d6a

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open Real Set MeasureTheory Kyprianou.Ch01
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    (∫ r : ℝ in Set.Ioi (1 : ℝ), r ^ (-alpha)) =
      1 / (alpha - 1) := by
  have hpower : -alpha < (-1 : ℝ) := by linarith
  rw [integral_Ioi_rpow_of_lt hpower zero_lt_one]
  simp only [one_rpow]
  have hdenom : -alpha + 1 ≠ 0 := by linarith
  have hne : alpha - 1 ≠ 0 := by linarith
  field_simp [hdenom, hne]
  ring
