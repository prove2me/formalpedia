-- Prove2me | solution 1 for GlobalTheory.T.nonempty_adicCompletion_quotient_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:32:00.509852+00:00
-- url     : https://prove2.me/submissions/c88e1267-fdb2-46c6-a011-c2f59584eef4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionQuotientRingEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionQuotientRingEquivStatement
import Theorems.Thm_GlobalTheory_adicCompletion_quotient_ringEquiv


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
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J q : Ideal A), Nonempty ((AdicCompletion J A ⧸ q.map (algebraMap A (AdicCompletion J A))) ≃+* AdicCompletion (J.map (Ideal.Quotient.mk q)) (A ⧸ q)) := by
  first | exact @GlobalTheory.adicCompletion_quotient_ringEquiv | exact GlobalTheory.adicCompletion_quotient_ringEquiv | (intros; apply GlobalTheory.adicCompletion_quotient_ringEquiv <;> assumption)
end _root_.GlobalTheory.T
