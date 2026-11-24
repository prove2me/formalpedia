-- Prove2me | solution 1 for GlobalTheory.T.small_rank_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:22:18.393961+00:00
-- url     : https://prove2.me/submissions/06dc368d-046a-4f86-a9b1-7bca3457fd88

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SmallRankBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SmallRankBoundStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_smallRank


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
  first | exact @GlobalTheory.CompanionTheory.InertZeta.smallRank | exact GlobalTheory.CompanionTheory.InertZeta.smallRank | (intros; apply GlobalTheory.CompanionTheory.InertZeta.smallRank <;> assumption)
end _root_.GlobalTheory.T
