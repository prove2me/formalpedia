-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplexVolume_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:14:27.409237+00:00
-- url     : https://prove2.me/submissions/c1d8a2af-f75a-49f8-80a0-117e53d561f4

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open scoped BigOperators Topology

theorem solution :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ (1 : ℝ)}) = 1 := by
  have hvol :
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ)) Set.univ = 1 := by
    exact MeasureTheory.Measure.pi_empty_univ
      (fun _ : Fin 0 => (MeasureTheory.volume : MeasureTheory.Measure ℝ))
  simpa using congrArg ENNReal.toReal hvol
