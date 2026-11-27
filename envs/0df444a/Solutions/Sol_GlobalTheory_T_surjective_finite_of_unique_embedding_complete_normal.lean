-- Prove2me | solution 1 for GlobalTheory.T.surjective_finite_of_unique_embedding_complete_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:34:09.493959+00:00
-- url     : https://prove2.me/submissions/2e05c1a7-4a3b-42af-91bd-f5f677a3f8e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveFiniteOfUniqueEmbeddingCompleteNormal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveFiniteOfUniqueEmbeddingCompleteNormalStatement
import Theorems.Thm_GlobalTheory_DegreeOne_surjective_of_unique_injective_localHom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
theorem _root_.solution : ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [IsIntegrallyClosed B] [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (ψ : B →+* R), IsAdicComplete (maximalIdeal B) B → Function.Injective ψ → ψ.Finite → (∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [CharZero R'], IsAdicComplete (maximalIdeal R') R' → ∀ f g : R →+* R', Function.Injective f → Function.Injective g → IsLocalHom f → IsLocalHom g → f.comp ψ = g.comp ψ → f = g) → Function.Surjective ψ := by
  first | exact @GlobalTheory.DegreeOne.surjective_of_unique_injective_localHom | exact GlobalTheory.DegreeOne.surjective_of_unique_injective_localHom | (intros; apply GlobalTheory.DegreeOne.surjective_of_unique_injective_localHom <;> assumption)
end _root_.GlobalTheory.T
