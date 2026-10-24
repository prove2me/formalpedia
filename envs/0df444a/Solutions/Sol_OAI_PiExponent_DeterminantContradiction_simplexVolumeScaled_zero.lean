-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:44:11.626928+00:00
-- url     : https://prove2.me/submissions/f046f73f-4484-4d5d-9c56-7d270513b5bb

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
open scoped BigOperators

theorem solution (r : Real) (hr : 0 ≤ r) :
    MeasureTheory.volume
        {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
      ENNReal.ofReal (r ^ 0 / (Nat.factorial 0 : Real)) := by
  have hset :
      {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} = Set.univ := by
    ext x
    simp [hr]
  have hvol : (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → Real)) =
      MeasureTheory.Measure.pi (fun _ : Fin 0 => (MeasureTheory.volume : MeasureTheory.Measure Real)) := rfl
  rw [hset, hvol, MeasureTheory.Measure.pi_empty_univ]
  simp