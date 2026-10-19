-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.volume_smul_image
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:47:26.934678+00:00
-- url     : https://prove2.me/submissions/cd4c4ede-909d-45df-89ec-2035aeecae95

import Mathlib

open scoped BigOperators
theorem solution (k : ℕ) (U : ℝ) (hU : 0 < U)
    (s : Set (Fin k → ℝ)) (hs : MeasurableSet s) :
    (MeasureTheory.volume ((fun x : Fin k → ℝ => U • x) '' s)).toReal =
      (U ^ k) * (MeasureTheory.volume s).toReal := by
  rw [Set.image_smul, MeasureTheory.Measure.addHaar_smul, Module.finrank_fin_fun, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), abs_of_pos (pow_pos hU k)]
