-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standard_simplex_volume_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T02:25:58.665825+00:00
-- url     : https://prove2.me/submissions/933de022-f731-49f6-b645-e62192920a25

import Mathlib

open scoped BigOperators Topology

theorem solution :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ (1 : ℝ)}) =
      1 / (Nat.factorial 0 : ℝ) := by
  have hset :
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ (1 : ℝ)} = Set.univ := by
    ext x
    simp
  rw [hset]
  simp [MeasureTheory.volume_pi, Nat.factorial]