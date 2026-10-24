-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_volume_zero_aux
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:20:58.030663+00:00
-- url     : https://prove2.me/submissions/68c71c2a-fe6e-44e2-8f27-b7385557d9ad

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem solution (T : Real) (hT : 0 < T) :
    MeasureTheory.volume {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} =
      ENNReal.ofReal (T ^ 0 / (Nat.factorial 0 : Real)) := by
  have hset : {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} = Set.univ := by
    ext x
    simp [hT]
  have hvol : MeasureTheory.volume (Set.univ : Set (Fin 0 → Real)) = 1 := by
    rw [← Set.pi_univ (Set.univ : Set (Fin 0))]
    rw [MeasureTheory.volume_pi_pi]
    simp
  rw [hset, hvol]
  simp