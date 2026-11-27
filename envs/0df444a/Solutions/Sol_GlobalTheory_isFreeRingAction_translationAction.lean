-- Prove2me | solution 1 for GlobalTheory.isFreeRingAction_translationAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:31.985077+00:00
-- url     : https://prove2.me/submissions/cb825242-1456-4fdc-b54b-8cdd52dd5bcd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_isFreeRingAction_arrow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
universe w v u
open CategoryTheory
namespace GlobalTheory
theorem _root_.solution (G R : Type*) [Group G] [Finite G] [CommRing R] :
    letI := translationAction G R
    IsFreeRingAction G (G → R) :=
  letI := translationAction G R
  isFreeRingAction_arrow G R fun _ _ _ ↦ rfl
end GlobalTheory
