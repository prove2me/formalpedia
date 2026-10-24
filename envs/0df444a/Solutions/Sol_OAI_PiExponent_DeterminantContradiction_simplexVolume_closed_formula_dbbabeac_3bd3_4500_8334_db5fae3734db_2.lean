-- Prove2me | solution 2 for OAI.PiExponent.DeterminantContradiction.simplexVolume_closed_formula_dbbabeac_3bd3_4500_8334_db5fae3734db
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:38:58.40615+00:00
-- url     : https://prove2.me/submissions/539ea3f4-83ec-409d-ab41-5a95731a561e

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_unit
open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real)) := by
  apply OAI.PiExponent.DeterminantContradiction.simplexVolume_unit <;> assumption
