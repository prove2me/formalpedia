-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standard_simplex_unit_volume_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T22:11:34.28986+00:00
-- url     : https://prove2.me/submissions/1982beb0-1199-49e6-b624-e03c2a968c3f

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators Topology

theorem solution :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ (1 : ℝ)}) = 1 := by
  have hs :
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ (1 : ℝ)} =
        (Set.univ : Set (Fin 0 → ℝ)) := by
    ext x
    simp
  rw [hs]
  change ENNReal.toReal
    (MeasureTheory.Measure.pi
      (fun _ : Fin 0 => (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (Set.univ : Set (Fin 0 → ℝ))) = 1
  rw [MeasureTheory.Measure.pi_univ]
  simp