-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.lowIndexCount_pos
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T13:18:33.870729+00:00
-- url     : https://prove2.me/submissions/fbb821cb-d84b-4046-a29f-75db8f848ceb

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem solution {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < (lowIndexCount d H : ℝ) := by
  unfold lowIndexCount
  apply Nat.cast_pos.mpr
  apply Finset.card_pos.mpr
  refine ⟨0, ?_⟩
  rw [realWeightedSimplex]
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · intro i
    exact Nat.zero_lt_succ _
  · simp
    exact le_of_lt (mul_pos d.base.A_pos hH)