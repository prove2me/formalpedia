-- Prove2me | solution 1 for GlobalTheory.T.recursion_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:21:07.438172+00:00
-- url     : https://prove2.me/submissions/d0e15ed6-9154-41c1-8283-a5ae97aecc8b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_RecursionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_RecursionIdentityStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_step


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
theorem _root_.solution : Step := by
  first | exact @GlobalTheory.CompanionTheory.InertLevi.step | exact GlobalTheory.CompanionTheory.InertLevi.step | (intros; apply GlobalTheory.CompanionTheory.InertLevi.step <;> assumption)
end _root_.GlobalTheory.T
