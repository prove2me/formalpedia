-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_base_case
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:40:26.390136+00:00
-- url     : https://prove2.me/submissions/64fccd28-b10d-43b8-8bd1-3aca400a38e8

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Nat.Factorial.Basic

open scoped BigOperators Topology

theorem solution :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ (1 : ℝ)}) =
    ((Nat.factorial 0 : ℕ) : ℝ)⁻¹ := by
  have hset :
      ({x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ (1 : ℝ)} :
        Set (Fin 0 → ℝ)) = Set.Icc (0 : Fin 0 → ℝ) 0 := by
    ext x
    constructor
    · intro _
      have hx : x = (0 : Fin 0 → ℝ) := Subsingleton.elim _ _
      simpa [hx]
    · intro _
      simp
  rw [hset, Real.volume_Icc_pi]
  simp
