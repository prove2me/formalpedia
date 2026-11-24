-- Prove2me | solution 1 for GlobalTheory.Pat.isCplAt_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:18:24.389148+00:00
-- url     : https://prove2.me/submissions/1010738f-3d6d-4d1c-b042-3931ebf4ab65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniversalLocalHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniqueUpToIso
import Theorems.Thm_GlobalTheory_T_completion_universal_local_hom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat
open GlobalTheory GlobalTheory.Pat
namespace GlobalTheory.Pat
theorem _root_.solution : ∀ (R S S' : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S'] (q : Ideal R) [q.IsPrime] (φ : R →+* S) (φ' : R →+* S'), IsCplAt q φ → IsCplAt q φ' → ∃ e : S ≃+* S', (e : S →+* S').comp φ = φ' := by
  intro R S S' _ _ _ _ _ q _ φ φ' h h'
  haveI := h.complete
  haveI := h'.complete
  obtain ⟨θ, ⟨hθl, hθ⟩, -⟩ := GlobalTheory.T.completion_universal_local_hom R S S' q φ φ' h h'.comap_eq
  obtain ⟨η, ⟨hηl, hη⟩, -⟩ := GlobalTheory.T.completion_universal_local_hom R S' S q φ' φ h' h.comap_eq
  have u := (GlobalTheory.T.completion_universal_local_hom R S S q φ φ h h.comap_eq).unique
    (y₁ := η.comp θ) (y₂ := RingHom.id S)
    ⟨RingHom.isLocalHom_comp η θ, by rw [RingHom.comp_assoc, hθ, hη]⟩
    ⟨inferInstance, RingHom.id_comp φ⟩
  have u' := (GlobalTheory.T.completion_universal_local_hom R S' S' q φ' φ' h' h'.comap_eq).unique
    (y₁ := θ.comp η) (y₂ := RingHom.id S')
    ⟨RingHom.isLocalHom_comp θ η, by rw [RingHom.comp_assoc, hη, hθ]⟩
    ⟨inferInstance, RingHom.id_comp φ'⟩
  exact ⟨RingEquiv.ofRingHom θ η u' u, hθ⟩
end GlobalTheory.Pat
