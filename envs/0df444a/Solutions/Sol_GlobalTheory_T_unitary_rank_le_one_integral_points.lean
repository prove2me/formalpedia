-- Prove2me | solution 1 for GlobalTheory.T.unitary_rank_le_one_integral_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:26:10.136795+00:00
-- url     : https://prove2.me/submissions/605dcc19-006b-446d-90a0-4ddec6702949

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryRankLeOneIntegralPoints
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryRankLeOneIntegralPointsStatement
import Theorems.Thm_GlobalTheory_InertZeta_smallRank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : SmallRank := by
  first | exact @GlobalTheory.InertZeta.smallRank | exact GlobalTheory.InertZeta.smallRank | (intros; apply GlobalTheory.InertZeta.smallRank <;> assumption)
end _root_.GlobalTheory.T
