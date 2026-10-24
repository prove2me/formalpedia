-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:06:14.762792+00:00
-- url     : https://prove2.me/submissions/1b031a7f-69fb-462d-920e-46eb1ce71eca

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_simplexRegion
import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_unit_volume_by_dimension

open scoped BigOperators

open MeasureTheory Filter Topology in

theorem solution : MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion 0 1) = ENNReal.ofReal (1 / (Nat.factorial (0 + 1) : Real)) := by
  exact OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_by_dimension 0
