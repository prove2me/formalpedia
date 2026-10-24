-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_mul_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:38:09.489132+00:00
-- url     : https://prove2.me/submissions/b90e1833-e077-4603-ac71-e59dc7c57836

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_succ_slice
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitInterval_integral_one_sub_pow

open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} *
        ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_slice,
    OAI.PiExponent.DeterminantContradiction.unitInterval_integral_one_sub_pow]