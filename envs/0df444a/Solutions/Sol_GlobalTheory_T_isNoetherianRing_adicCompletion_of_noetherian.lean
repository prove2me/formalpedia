-- Prove2me | solution 1 for GlobalTheory.T.isNoetherianRing_adicCompletion_of_noetherian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:55:18.920132+00:00
-- url     : https://prove2.me/submissions/b3ba647a-13d9-411c-9d2d-38cbae4e117f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherianStatement
import Theorems.Thm_GlobalTheory_AdicNoeth_isNoetherianRing_adicCompletion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsNoetherianRing (AdicCompletion I R) := by
  first | exact @GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion | exact GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion | (intros; apply GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion <;> assumption)
end _root_.GlobalTheory.T
