-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.integratedScaledSimplexVolume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:28:10.704495+00:00
-- url     : https://prove2.me/submissions/66d83d5a-bc2c-493b-8963-2643295f39fc

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexSliceVolume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexPowerIntegral
open scoped BigOperators

theorem solution (n : Nat) :
    ∫⁻ t in Set.Icc (0 : Real) 1,
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1 - t}
      ∂MeasureTheory.volume =
    ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by
  rw [← OAI.PiExponent.DeterminantContradiction.simplexPowerIntegral n]
  apply MeasureTheory.lintegral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
  exact OAI.PiExponent.DeterminantContradiction.simplexSliceVolume n t ht