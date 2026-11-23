-- Prove2me | solution 1 for IntegerRootsFN.Main.elementary_search_data
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:47:59.800959+00:00
-- url     : https://prove2.me/submissions/3b65984d-9acb-4b66-9474-a033e5a037b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_Binary
import Definitions.Def_IntegerRootsFN_Main_ElementarySearch
import Theorems.Thm_IntegerRootsFN_Main_elementary_search_coverage
import Theorems.Thm_IntegerRootsFN_Main_elementary_search_statistics

set_option autoImplicit false

open IntegerRootsFN.Main

theorem solution :
    ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
      (∀ r : ℤ, f.IsRoot r → 2 ≤ |r| → r ∈ searchCandidates f n b) ∧
      (searchCandidates f n b).length ≤ 21 * min n b ∧
      (pointSize (searchCandidates f n b) : ℝ) ≤
        21 * (5 * (min n b : ℕ) + (b : ℝ) + (1 : ℝ) / 2 * logTwo ((min n b : ℕ) + 1)) := by
  intro n b f hf
  exact ⟨IntegerRootsFN.Main.elementary_search_coverage n b f hf,
    IntegerRootsFN.Main.elementary_search_statistics n b f hf⟩