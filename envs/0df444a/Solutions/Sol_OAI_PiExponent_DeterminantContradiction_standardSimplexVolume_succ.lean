-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplexVolume_succ
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T02:17:45.234929+00:00
-- url     : https://prove2.me/submissions/b91574d9-64e9-4ba7-b339-b98eded83154

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_eq_scaledSliceIntegral
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_scaledSliceIntegral_eval

open scoped BigOperators Topology

theorem solution (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ (1 : ℝ)}) =
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) / (n + 1 : ℝ) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_scaledSliceIntegral,
    OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_eval]
  have hn : (0 : ℝ) ≤ 1 / (n + 1 : ℝ) := by positivity
  rw [ENNReal.toReal_ofReal hn]
  ring