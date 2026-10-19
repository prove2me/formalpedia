-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.translatedIndexWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T13:12:21.596745+00:00
-- url     : https://prove2.me/submissions/f0906ab5-e5bc-4363-8d0a-8539e7c6c14f

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem solution {nu : ℝ} (d : FixedData nu) {H : ℝ} (a : indices d H) :
    0 ≤ translatedIndexWeight d a := by
  classical
  unfold translatedIndexWeight MatrixArithmetic.logWeights
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)