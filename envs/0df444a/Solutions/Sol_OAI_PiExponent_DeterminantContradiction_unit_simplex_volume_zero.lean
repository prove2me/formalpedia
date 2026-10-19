-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unit_simplex_volume_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T03:14:54.347033+00:00
-- url     : https://prove2.me/submissions/cdb3aca5-33d9-4d23-8f51-0a7a78e20ccc

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators

theorem solution :
    (MeasureTheory.volume (Set.univ : Set (Fin 0 → ℝ))).toReal = 1 := by
  simp only [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_empty_univ,
    ENNReal.toReal_one]
