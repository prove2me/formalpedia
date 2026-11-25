-- Prove2me | solution 1 for GlobalTheory.T.sphericalInductionTransitivity_of_leviExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:27:51.392877+00:00
-- url     : https://prove2.me/submissions/64f64b71-2760-4093-b613-0a122f70a8e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SphericalInductionTransitivityOfLeviExists
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SphericalInductionTransitivityOfLeviExistsStatement
import Theorems.Thm_GlobalTheory_InertZeta_sphTrans


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
theorem _root_.solution : LeviExists → SphTrans := by
  first | exact @GlobalTheory.InertZeta.sphTrans | exact GlobalTheory.InertZeta.sphTrans | (intros; apply GlobalTheory.InertZeta.sphTrans <;> assumption)
end _root_.GlobalTheory.T
