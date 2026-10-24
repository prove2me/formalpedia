-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:24:15.065+00:00
-- url     : https://prove2.me/submissions/5bc8c557-6019-4540-88d8-1aa58eecc644

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_unit
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_scale
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_negative

open MeasureTheory

theorem solution (n : Nat) (c : Real) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ c} =
      (if 0 ≤ c then ENNReal.ofReal (c ^ n / (Nat.factorial n : Real)) else 0) := by
  classical
  by_cases hc : 0 ≤ c
  · rw [if_pos hc,
      OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_scale n c hc,
      OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_unit n]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ c ^ n)]
    congr 1
    ring
  · have hneg : c < 0 := lt_of_not_ge hc
    rw [if_neg hc,
      OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_negative n c hneg]