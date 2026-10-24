-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unit_simplex_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:39:06.654347+00:00
-- url     : https://prove2.me/submissions/8ffc919a-a7e1-4d0c-b4b3-9252c2f2087b

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_power_integral_dbbabeac_3bd3_4500_8334_db5fae3734db

theorem solution (n : Nat) :
    (∫ t in (0 : Real)..1, (1 - t) ^ n) = 1 / ((n + 1 : Nat) : Real) := by
  apply OAI.PiExponent.DeterminantContradiction.simplex_power_integral_dbbabeac_3bd3_4500_8334_db5fae3734db <;> assumption
