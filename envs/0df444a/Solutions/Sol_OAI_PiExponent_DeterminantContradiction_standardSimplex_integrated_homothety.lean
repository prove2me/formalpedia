-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_integrated_homothety
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:20:39.677302+00:00
-- url     : https://prove2.me/submissions/bfe4ba80-0453-4dc0-8930-0119bba50f06

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_fiber_volume_homothety
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_lintegral_congr_on_Icc
open scoped BigOperators

theorem solution (n : Nat) :
    ∫⁻ t in Set.Icc (0 : Real) 1,
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1 - t}
      ∂MeasureTheory.volume =
    ∫⁻ t in Set.Icc (0 : Real) 1,
      (ENNReal.ofReal (1 - t) ^ n *
        MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1})
      ∂MeasureTheory.volume := by
  apply OAI.PiExponent.DeterminantContradiction.lintegral_congr_on_Icc
  intro t ht
  exact OAI.PiExponent.DeterminantContradiction.standardSimplex_fiber_volume_homothety
    n (1 - t) (sub_nonneg.mpr ht.2)