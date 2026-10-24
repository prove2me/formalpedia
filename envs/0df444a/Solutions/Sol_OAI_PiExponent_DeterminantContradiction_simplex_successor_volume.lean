-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_successor_volume
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:06:15.633969+00:00
-- url     : https://prove2.me/submissions/9cb9ca37-4071-44f7-92cd-d845c51e78d7

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_simplexRegion
import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_unit_volume_by_dimension

open scoped BigOperators

open MeasureTheory Filter Topology in

theorem solution (n : Nat) : MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion (n + 1) 1) = ENNReal.ofReal (1 / (n + 2 : Real)) * MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion n 1) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_by_dimension,
    OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_by_dimension,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ (n+1)]; push_cast; field_simp; ring
