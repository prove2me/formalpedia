-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_zero_47e3ceaa
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:36:04.881302+00:00
-- url     : https://prove2.me/submissions/ebb8f218-3f4f-4c40-9c79-7afa6b611a24

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
open scoped BigOperators

theorem solution :
    MeasureTheory.volume
        {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / ((Nat.factorial 0 : Nat) : Real)) := by
  have hset :
      ({x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} :
          Set (Fin 0 → Real)) = Set.univ := by
    ext x
    simp
  rw [hset]
  rw [MeasureTheory.Measure.volume_pi_eq_dirac (ι := Fin 0) (α := fun _ => Real)]
  simp [Nat.factorial]
