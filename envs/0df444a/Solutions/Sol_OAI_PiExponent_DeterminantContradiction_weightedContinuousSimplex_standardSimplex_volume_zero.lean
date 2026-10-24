-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_standardSimplex_volume_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:11:41.433439+00:00
-- url     : https://prove2.me/submissions/b88cf877-a070-47a7-ac7f-0a48692dfae6

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
open scoped BigOperators

theorem solution
    (T : Real) (hT : 0 < T) :
    MeasureTheory.volume {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} =
      ENNReal.ofReal (T ^ 0 / (Nat.factorial 0 : Real)) := by
  have hset :
      {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} = Set.univ := by
    ext x
    simp [hT]
  rw [hset, MeasureTheory.Measure.volume_pi_eq_dirac]
  simp