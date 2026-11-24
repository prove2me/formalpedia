-- Prove2me | solution 1 for GlobalTheory.T.generating_function_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:11:02.352987+00:00
-- url     : https://prove2.me/submissions/3468b256-bb69-41df-a1cf-ba9e0e41479b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_GeneratingFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_GeneratingFunctionIdentityStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_InertGenFun_genFun


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
theorem _root_.solution : GenFun := by
  first | exact @GlobalTheory.CompanionTheory.InertGenFun.genFun | exact GlobalTheory.CompanionTheory.InertGenFun.genFun | (intros; apply GlobalTheory.CompanionTheory.InertGenFun.genFun <;> assumption)
end _root_.GlobalTheory.T
