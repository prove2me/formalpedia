-- Prove2me | solution 2 for Kurodoko.NPC.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:13:55.726735+00:00
-- url     : https://prove2.me/submissions/66bd76ff-d35f-4930-914c-5d0ae372a916
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_Kurodoko_NPC_Puzzle
import Definitions.Def_Kurodoko_NPC_OneInThreeSat
import Definitions.Def_Kurodoko_NPC_Reduction
import Theorems.Thm_CookPvsNP_polyReducible_trans
import Theorems.Thm_Kurodoko_NPC_reduction_correct

open Kurodoko.NPC CookPvsNP ProjSchedTW.Complexity

theorem solution (h3 : NPComplete oneInThreeLang) :
    ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : Lang Sym'),
      L' ∈ NP Sym' → PolyReducible L' kurodokoLang := by
  intro Sym' _ _ L' hL'
  exact polyReducible_trans (h3.2 Sym' L' hL') ⟨reduceWord, reduction_correct.1, reduction_correct.2⟩
