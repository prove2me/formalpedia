-- Prove2me | solution 1 for NadlerCLS.theorem_C_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:30:51.758389+00:00
-- url     : https://prove2.me/submissions/6dfb2dac-4942-43da-8075-274a3583cfa7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NadlerCLS_coSearch
import Definitions.Def_NadlerCLS_holderSearch
import Theorems.Thm_NadlerCLS_theorem_C_2_bounded

set_option autoImplicit false

open NetworkEquilibriumCLS.LinearNash

open NadlerCLS in
theorem solution (n : ℕ) (hn : 1 ≤ n) (β : ℚ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    SearchReduces (holderSearch n β) (coSearch n) := by
  obtain ⟨k, F, G, hF, hG, H⟩ := theorem_C_2_bounded n hn β hβ0 hβ1
  exact ⟨F, G, hF, hG, fun s hs => ⟨(H s hs).1, fun t ht => ((H s hs).2 t ht).1⟩⟩
