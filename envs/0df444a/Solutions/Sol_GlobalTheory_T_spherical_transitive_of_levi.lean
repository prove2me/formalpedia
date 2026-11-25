-- Prove2me | solution 1 for GlobalTheory.T.spherical_transitive_of_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:32:31.081926+00:00
-- url     : https://prove2.me/submissions/95e8d13f-f020-43fb-81cc-e605428dea3e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SphericalTransitiveOfLevi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SphericalTransitiveOfLeviStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_InertTrans_sphTrans_of_leviExists


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
  first | exact @GlobalTheory.CompanionTheory.InertTrans.sphTrans_of_leviExists | exact GlobalTheory.CompanionTheory.InertTrans.sphTrans_of_leviExists | (intros; apply GlobalTheory.CompanionTheory.InertTrans.sphTrans_of_leviExists <;> assumption)
end _root_.GlobalTheory.T
