-- Prove2me | solution 1 for GlobalTheory.adicCompletion_quotient_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:17.719091+00:00
-- url     : https://prove2.me/submissions/10c1052a-4919-4d9f-88a4-54b6caf12121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionQuotientRingEquiv
import Theorems.Thm_GlobalTheory_AdicQuot_ker_psi
import Theorems.Thm_GlobalTheory_AdicQuot_psi_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
namespace GlobalTheory
theorem _root_.solution :
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J q : Ideal A),
      Nonempty ((AdicCompletion J A ⧸ q.map (algebraMap A (AdicCompletion J A))) ≃+*
        AdicCompletion (J.map (Ideal.Quotient.mk q)) (A ⧸ q)) := by
  intro A _ _ J q
  exact ⟨(Ideal.quotEquivOfEq (GlobalTheory.AdicQuot.ker_psi J q).symm).trans
    (RingHom.quotientKerEquivOfSurjective (GlobalTheory.AdicQuot.psi_surjective J q))⟩
end GlobalTheory
