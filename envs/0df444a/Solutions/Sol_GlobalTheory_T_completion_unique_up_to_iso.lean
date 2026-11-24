-- Prove2me | solution 1 for GlobalTheory.T.completion_unique_up_to_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:33:59.827991+00:00
-- url     : https://prove2.me/submissions/ad3bec5c-6362-4f63-80b4-683f3d306af3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniqueUpToIso
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniqueUpToIsoStatement
import Theorems.Thm_GlobalTheory_Pat_isCplAt_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R S S' : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S'] (q : Ideal R) [q.IsPrime] (φ : R →+* S) (φ' : R →+* S'), IsCplAt q φ → IsCplAt q φ' → ∃ e : S ≃+* S', (e : S →+* S').comp φ = φ' := by
  first | exact @GlobalTheory.Pat.isCplAt_unique | exact GlobalTheory.Pat.isCplAt_unique | (intros; apply GlobalTheory.Pat.isCplAt_unique <;> assumption)
end _root_.GlobalTheory.T
