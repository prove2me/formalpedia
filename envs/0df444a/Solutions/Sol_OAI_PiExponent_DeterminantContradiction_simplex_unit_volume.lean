-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_unit_volume
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:38:59.658356+00:00
-- url     : https://prove2.me/submissions/12b261c4-147d-428d-a29b-4b3290a20cb2

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_simplexRegion
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_unit_volume_by_dimension

open scoped BigOperators

theorem solution (n : Nat) : MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion n 1) = ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by
  apply OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_by_dimension <;> assumption
