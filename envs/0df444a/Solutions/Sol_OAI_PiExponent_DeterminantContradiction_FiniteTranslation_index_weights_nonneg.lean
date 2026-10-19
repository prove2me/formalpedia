-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_weights_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:10:07.610024+00:00
-- url     : https://prove2.me/submissions/d7851032-4da2-455e-98ad-a996ff4837f2

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution {nu : ℝ} (d : FixedData nu) {H : ℝ} :
    ∀ a : Index d H, 0 ≤ weight d a := by
  intro a
  unfold weight
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg
  · exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _