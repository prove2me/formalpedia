-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_volume_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:38:41.040709+00:00
-- url     : https://prove2.me/submissions/ba634bfd-bc84-4155-8888-89fc64d0ad31

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem solution :
    MeasureTheory.volume
        {y : Fin 0 → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial 0 : Real)) := by
  have hset :
      {y : Fin 0 → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1} =
        Set.pi Set.univ (fun _ : Fin 0 => (Set.univ : Set Real)) := by
    ext y
    simp
  rw [hset, MeasureTheory.volume_pi_pi]
  simp