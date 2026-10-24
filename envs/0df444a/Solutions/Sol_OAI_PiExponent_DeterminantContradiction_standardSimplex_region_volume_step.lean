-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume_step
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:23:15.884694+00:00
-- url     : https://prove2.me/submissions/56b3d191-9557-482f-a75b-bb0e50037059

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_region_volume_slicing
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_region_volume_integral

open scoped BigOperators

 theorem solution {m : Nat} (H : Real) (hH : 0 < H)
    (ih : ∀ (T : Real), 0 < T →
      (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ T}).toReal =
        T ^ m / ((Nat.factorial m : Nat) : Real)) :
    (MeasureTheory.volume {x : Fin (m + 1) → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H}).toReal =
      H ^ (m + 1) / ((Nat.factorial (m + 1) : Nat) : Real) := by
  rw [OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume_slicing m H hH]
  exact OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume_integral m H hH ih