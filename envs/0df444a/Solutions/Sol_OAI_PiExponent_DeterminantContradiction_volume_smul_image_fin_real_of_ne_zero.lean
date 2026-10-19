-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.volume_smul_image_fin_real_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T22:01:24.767923+00:00
-- url     : https://prove2.me/submissions/f3198ad9-755b-494e-9e29-1d3216b18427

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.ENNReal.Real

open scoped BigOperators Topology Pointwise

theorem solution
    (m : ℕ) (T : ℝ) (hT : 0 ≤ T) (hT0 : T ≠ 0) (s : Set (Fin m → ℝ)) :
    ENNReal.toReal (MeasureTheory.volume ((fun x : Fin m → ℝ => T • x) '' s)) =
      T ^ m * ENNReal.toReal (MeasureTheory.volume s) := by
  change ENNReal.toReal (MeasureTheory.volume (T • s)) = _
  rw [MeasureTheory.Measure.addHaar_smul_of_nonneg MeasureTheory.volume hT s,
    Module.finrank_pi, Fintype.card_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hT m)]
