-- Prove2me | solution 1 for GlobalTheory.T.dual_pairing_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:06:43.585914+00:00
-- url     : https://prove2.me/submissions/00149903-6a88-4178-bc43-d7241938010b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_DualPairingExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_DualPairingExistsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_InertDual_dual


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
theorem _root_.solution : Dual := by
  first | exact @GlobalTheory.CompanionTheory.InertDual.dual | exact GlobalTheory.CompanionTheory.InertDual.dual | (intros; apply GlobalTheory.CompanionTheory.InertDual.dual <;> assumption)
end _root_.GlobalTheory.T
