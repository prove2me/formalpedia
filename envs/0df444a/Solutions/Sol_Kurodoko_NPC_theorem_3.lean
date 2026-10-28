-- Prove2me | solution 1 for Kurodoko.NPC.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T05:40:46.627878+00:00
-- url     : https://prove2.me/submissions/32dabde9-9a58-4acc-9788-7a23ed430d4f
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

open CookPvsNP ProjSchedTW.Complexity Kurodoko.NPC

theorem solution (h3 : NPComplete oneInThreeLang) :
    ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : Lang Sym'),
      L' ∈ NP Sym' → PolyReducible L' kurodokoLang :=
  fun Sym' _ _ L' hL' =>
    polyReducible_trans (h3.2 Sym' L' hL') ⟨reduceWord, reduction_correct.1, reduction_correct.2⟩
