-- Prove2me | solution 1 for GlobalTheory.T.completion_universal_local_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:05:27.652056+00:00
-- url     : https://prove2.me/submissions/5f92815f-3fc4-4a0f-ac37-15ce5dfbed07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniversalLocalHom
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniversalLocalHomStatement
import Theorems.Thm_GlobalTheory_Pat_isCplAt_existsUnique_map


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
theorem _root_.solution : ∀ (R S S' : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S'] [IsAdicComplete (maximalIdeal S') S'] (q : Ideal R) [q.IsPrime] (φ : R →+* S) (ψ : R →+* S'), IsCplAt q φ → (maximalIdeal S').comap ψ = q → ∃! θ : S →+* S', IsLocalHom θ ∧ θ.comp φ = ψ := by
  first | exact @GlobalTheory.Pat.isCplAt_existsUnique_map | exact GlobalTheory.Pat.isCplAt_existsUnique_map | (intros; apply GlobalTheory.Pat.isCplAt_existsUnique_map <;> assumption)
end _root_.GlobalTheory.T
