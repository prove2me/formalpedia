-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial_aux_base
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:40:39.474603+00:00
-- url     : https://prove2.me/submissions/366f57eb-9249-4f1c-9a1b-50f7d89c5f32

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem solution :
    MeasureTheory.volume
      {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin 0 => x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial 0 : Real)) := by
  have hset :
      {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin 0 => x i) ≤ 1} = Set.univ := by
    ext x
    simp
  rw [hset]
  simp [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_of_empty,
    Nat.factorial_zero]