-- Prove2me | solution 1 for GlobalTheory.T.count_of_heisenberg_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:05:35.667147+00:00
-- url     : https://prove2.me/submissions/065eee8a-54fb-416e-b49f-e611894b04bd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CountOfHeisenbergIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CountOfHeisenbergIndexStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_count


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
theorem _root_.solution : Heis → LatIndex → TraceIndex → Count := by
  first | exact @GlobalTheory.CompanionTheory.InertCount.count | exact GlobalTheory.CompanionTheory.InertCount.count | (intros; apply GlobalTheory.CompanionTheory.InertCount.count <;> assumption)
end _root_.GlobalTheory.T
