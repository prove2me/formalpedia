-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_factorial_base
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T02:21:03.27717+00:00
-- url     : https://prove2.me/submissions/3b30a471-a0ea-48b6-b70c-b8dedcd4e569

import Mathlib

open scoped BigOperators

theorem solution :
    (MeasureTheory.volume
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ 1}).toReal = 1 := by
  have hset :
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ 1} = Set.univ := by
    ext x
    simp
  rw [hset, MeasureTheory.volume_pi]
  simp