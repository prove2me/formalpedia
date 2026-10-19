-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:39:12.058692+00:00
-- url     : https://prove2.me/submissions/cd77ea91-39ad-48f5-ae95-b88e236329bb

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators Topology

theorem solution :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ (1 : ℝ)}) = 1 := by
  have hset : {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ (1 : ℝ)} =
      (Set.univ : Set (Fin 0 → ℝ)) := by
    ext x
    simp
  rw [hset, MeasureTheory.volume_pi, MeasureTheory.Measure.pi_empty_univ,
    ENNReal.toReal_one]