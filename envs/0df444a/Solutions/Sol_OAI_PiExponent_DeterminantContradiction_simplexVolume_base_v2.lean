-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_base_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:13:35.664363+00:00
-- url     : https://prove2.me/submissions/424d7e0f-e44d-4f95-a1d9-ebe6cf2436b1

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem solution :
    MeasureTheory.volume
        {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial 0 : Real)) := by
  have hset :
      {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
        (Set.univ : Set (Fin 0 → Real)) := by
    ext x
    simp
  rw [hset, ← Set.pi_univ (Set.univ : Set (Fin 0))]
  rw [MeasureTheory.volume_pi_pi]
  simp