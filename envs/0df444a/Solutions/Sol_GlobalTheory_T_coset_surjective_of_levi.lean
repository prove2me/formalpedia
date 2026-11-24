-- Prove2me | solution 1 for GlobalTheory.T.coset_surjective_of_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:34:00.872366+00:00
-- url     : https://prove2.me/submissions/caafc6cd-f43f-4c5e-801a-d3d5a8014c00

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetSurjectiveOfLevi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetSurjectiveOfLeviStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_cosetSurj


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
theorem _root_.solution : LeviExists → CosetSurj := by
  first | exact @GlobalTheory.CompanionTheory.InertCoset.cosetSurj | exact GlobalTheory.CompanionTheory.InertCoset.cosetSurj | (intros; apply GlobalTheory.CompanionTheory.InertCoset.cosetSurj <;> assumption)
end _root_.GlobalTheory.T
