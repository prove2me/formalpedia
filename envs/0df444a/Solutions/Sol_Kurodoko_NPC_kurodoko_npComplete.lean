-- Prove2me | solution 1 for Kurodoko.NPC.kurodoko_npComplete
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T05:40:46.083889+00:00
-- url     : https://prove2.me/submissions/bf7e5843-58b2-452d-91de-01786f01d57c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_Kurodoko_NPC_Puzzle
import Definitions.Def_Kurodoko_NPC_OneInThreeSat
import Theorems.Thm_Kurodoko_NPC_theorem_2
import Theorems.Thm_Kurodoko_NPC_theorem_3

open CookPvsNP ProjSchedTW.Complexity Kurodoko.NPC

theorem solution (h3 : NPComplete oneInThreeLang) : NPComplete kurodokoLang :=
  ⟨theorem_2, theorem_3 h3⟩
