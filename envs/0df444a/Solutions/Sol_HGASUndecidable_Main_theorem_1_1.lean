-- Prove2me | solution 1 for HGASUndecidable.Main.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:01:26.085452+00:00
-- url     : https://prove2.me/submissions/7d5a84cd-e960-4aad-bfd5-9b8521a89fd9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HGASUndecidable_Main_Codes
import Theorems.Thm_HGASUndecidable_Main_theorem_2_3
import Theorems.Thm_HGASUndecidable_Main_theorem_2_1
import Theorems.Thm_HGASUndecidable_Main_manyOneHard_not_computablePred

open Filter Topology MeasureTheory
open scoped BigOperators
open HGASUndecidable.Main

theorem solution : ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    ∀ d : ℕ, 3 ≤ d → Odd d → ManyOneComplete (HGAS n d) ∧ ¬ComputablePred (HGAS n d) := by
  obtain ⟨n₀, d₀, hn₀, hd₀, ⟨k₀, hk⟩, hmc⟩ := theorem_2_3
  subst d₀
  have hk₀ : 1 ≤ k₀ := by omega
  have hNk : k₀ ≤ n₀ + k₀ - 1 := by omega
  refine ⟨Nat.choose (n₀ + k₀ - 1) k₀, Nat.choose_pos hNk, ?_⟩
  intro n hn d hd hodd
  have hcomplete : ManyOneComplete (HGAS n d) :=
    (theorem_2_1 n₀ k₀ hn₀ hk₀ n d hn hd hodd).1 hmc
  exact ⟨hcomplete, manyOneHard_not_computablePred (HGAS n d) hcomplete.2⟩
