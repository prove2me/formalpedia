-- Prove2me | solution 1 for N25.Endgame.pQ25_degree
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:50.918463+00:00
-- url     : https://prove2.me/submissions/5ae88741-4c73-40d8-8f15-82b4fd450ea2

import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_N25_Endgame_cuspChoice25_spec

set_option autoImplicit false

namespace N25.Endgame

theorem _root_.solution (i : Fin 5) : (pQ25 i).deg = 1 := by
  exact (cuspChoice25_spec.2.2.2.1 i).1

end N25.Endgame
