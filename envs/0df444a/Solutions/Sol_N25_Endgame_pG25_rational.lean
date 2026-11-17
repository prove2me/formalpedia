-- Prove2me | solution 1 for N25.Endgame.pG25_rational
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:50.34991+00:00
-- url     : https://prove2.me/submissions/36cda4bf-e9b0-47a3-b271-c23b3c018533

import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_N25_Endgame_cuspChoice25_spec

set_option autoImplicit false

namespace N25.Endgame

theorem _root_.solution (i : Fin 5) : IsRationalGeomPlace (pG25 i) := by
  exact ⟨(cuspChoice25_spec.2.2.2.1 i).2, fun σ => cuspChoice25_spec.2.2.2.2.1 σ i⟩

end N25.Endgame
