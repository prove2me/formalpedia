-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_product_volume_scaling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:39:01.449985+00:00
-- url     : https://prove2.me/submissions/761d378c-7a4c-4bdd-a20b-f119ff1babe3

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_simplexRegion
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_scaling_by_cutoff

open scoped BigOperators

theorem solution (n : Nat) (T : Real) (hT : 0 < T) : MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion n T) = ENNReal.ofReal (T ^ (n + 1)) * MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion n 1) := by
  apply OAI.PiExponent.DeterminantContradiction.simplex_volume_scaling_by_cutoff <;> assumption
