-- Prove2me | solution 2 for Kurodoko.NPC.kurodoko_npComplete
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:13:56.35353+00:00
-- url     : https://prove2.me/submissions/83e832d0-aecb-4c6a-9664-31d02641f9ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_Kurodoko_NPC_Puzzle
import Definitions.Def_Kurodoko_NPC_OneInThreeSat
import Theorems.Thm_Kurodoko_NPC_theorem_2
import Theorems.Thm_Kurodoko_NPC_theorem_3

open Kurodoko.NPC CookPvsNP ProjSchedTW.Complexity

theorem solution (h3 : NPComplete oneInThreeLang) : NPComplete kurodokoLang :=
  ⟨theorem_2, theorem_3 h3⟩
