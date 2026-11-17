-- Prove2me | solution 1 for N25.Endgame.pG25_degree
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:49.731194+00:00
-- url     : https://prove2.me/submissions/77e109e4-5b84-4ebe-bca3-9788ddb35484

import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_N25_Endgame_cuspChoice25_spec

set_option autoImplicit false

namespace N25.Endgame

theorem _root_.solution (i : Fin 5) : (pG25 i).deg = 1 := by
  exact (cuspChoice25_spec.2.2.2.1 i).2

end N25.Endgame
