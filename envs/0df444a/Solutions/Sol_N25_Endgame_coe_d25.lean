-- Prove2me | solution 1 for N25.Endgame.coe_d25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:06.259819+00:00
-- url     : https://prove2.me/submissions/3c20d3c4-22b0-43bc-9680-e8bfc039a97b

import Definitions.Def_N25_CuspidalSubgroup
import Theorems.Thm_N25_Endgame_pG25_degree
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_N25_Endgame_pG25_rational
import Theorems.Thm_N25_Endgame_pointDiff_mem_M
import Definitions.Def_N25_PointDifference
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

namespace N25.Endgame

/-- The cuspidal generator `d25` is the difference of the first two selected geometric cusps. -/
theorem _root_.solution :
    (d25 : N25.J) = pointDiff (pG25 0) (pG25 1) ((pG25_degree 0).trans (pG25_degree 1).symm) := by
  rw [d25, dif_pos (show ∃ hd : (pG25 0).deg = (pG25 1).deg, pointDiff (pG25 0) (pG25 1) hd ∈ N25.M from
    ⟨(pG25_degree 0).trans (pG25_degree 1).symm,
      pointDiff_mem_M (pG25 0) (pG25 1) (pG25_rational 0) (pG25_rational 1)⟩)]

end N25.Endgame
