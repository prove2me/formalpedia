-- Prove2me | solution 1 for N25.U25_selected_rational_order
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:58:08.977401+00:00
-- url     : https://prove2.me/submissions/791cfefb-b29f-4901-ab0c-5943ebecf0c9

import Mathlib
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_Units
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_N25_Endgame_cuspChoice25_spec
import Theorems.Thm_N25_U25_selected_geometric_order
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_N25_UnitSeries
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar

set_option autoImplicit false

namespace N25

theorem _root_.solution (i j : Fin 5) :
    (N25.Endgame.pQ25 j).ord (U25 i) = unitOrders25 i j := by
  rw [← N25.Endgame.cuspChoice25_spec.2.2.2.2.2 j (U25 i)]
  exact U25_selected_geometric_order i j

end N25
