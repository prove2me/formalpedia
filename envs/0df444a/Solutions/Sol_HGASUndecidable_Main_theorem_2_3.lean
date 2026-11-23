-- Prove2me | solution 1 for HGASUndecidable.Main.theorem_2_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:52:06.000809+00:00
-- url     : https://prove2.me/submissions/109d388e-73c7-43d6-ab47-e9627f884bf7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HGASUndecidable_Main_Codes
import Theorems.Thm_HGASUndecidable_Main_lemma_7_2
import Theorems.Thm_HGASUndecidable_Main_proposition_4_4
import Theorems.Thm_HGASUndecidable_Main_haltingSet_manyOneHard
import Theorems.Thm_HGASUndecidable_Main_admissiblePower_exists
import Theorems.Thm_HGASUndecidable_Main_bounds94_exists
import Theorems.Thm_HGASUndecidable_Main_theorem_2_3_computable_reduction

open Filter Topology MeasureTheory
open scoped BigOperators
open HGASUndecidable.Main

theorem solution : ∃ n d : ℕ, 1 ≤ n ∧ 3 ≤ d ∧ Odd d ∧ ManyOneComplete (HGAS n d) := by
  obtain ⟨a, ha⟩ := lemma_7_2
  obtain ⟨M, hM⟩ := admissiblePower_exists a
  obtain ⟨M₀, K₀, hb⟩ := bounds94_exists a ha
  obtain ⟨f, hf, hred⟩ := theorem_2_3_computable_reduction a ha M hM M₀ K₀ hb
  refine ⟨compactDim a, M+9, by simp [compactDim], by omega, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hM.1
    exact ⟨k+4, by omega⟩
  · constructor
    · exact proposition_4_4.2.1 _ _
    · intro A hA
      exact (haltingSet_manyOneHard A hA).trans
        ⟨f, hf, fun e => (hred e).symm⟩
