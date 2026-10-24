-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_slice
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:47:46.458967+00:00
-- url     : https://prove2.me/submissions/5a062449-9677-4ca7-aa45-98ea20e5c05b

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_closed_formula_dbbabeac_3bd3_4500_8334_db5fae3734db
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_power_integral_dbbabeac_3bd3_4500_8334_db5fae3734db
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_factorial_step_dbbabeac_3bd3_4500_8334_db5fae3734db
open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} *
        ENNReal.ofReal (∫ t in (0 : Real)..1, (1 - t) ^ n) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplexVolume_closed_formula_dbbabeac_3bd3_4500_8334_db5fae3734db]
  rw [OAI.PiExponent.DeterminantContradiction.simplexVolume_closed_formula_dbbabeac_3bd3_4500_8334_db5fae3734db]
  rw [OAI.PiExponent.DeterminantContradiction.simplex_power_integral_dbbabeac_3bd3_4500_8334_db5fae3734db]
  exact OAI.PiExponent.DeterminantContradiction.simplex_factorial_step_dbbabeac_3bd3_4500_8334_db5fae3734db n