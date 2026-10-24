-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:12:19.735211+00:00
-- url     : https://prove2.me/submissions/8d887040-5524-4eb4-bdb3-02b0ce1939f9

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
open scoped BigOperators

theorem solution :
    MeasureTheory.volume
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
    ENNReal.ofReal 1 := by
  have hset :
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} = Set.univ := by
    ext x
    simp
  rw [hset, MeasureTheory.Measure.volume_pi_eq_dirac]
  simp