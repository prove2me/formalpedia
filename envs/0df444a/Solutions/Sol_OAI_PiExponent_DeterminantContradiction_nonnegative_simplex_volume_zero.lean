-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:24:11.599661+00:00
-- url     : https://prove2.me/submissions/a95f9895-38a7-4a98-a37e-35edeec9d751

import Mathlib

open scoped BigOperators

theorem solution (U : ℝ) (hU : 0 ≤ U) :
    (MeasureTheory.volume
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ U}).toReal =
      U ^ 0 / (Nat.factorial 0 : ℝ) := by
  have hset :
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ U} = Set.univ := by
    ext x
    simp [hU]
  rw [hset, MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]
  norm_num