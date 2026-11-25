-- Prove2me | solution 1 for GroundTheory.Arith.Etale.pullbackUnitApp_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:06:34.01992+00:00
-- url     : https://prove2.me/submissions/485de9cf-4b2b-401b-89c4-898a797a91bd

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohPresheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
variable {V T U : Scheme.{u}}
namespace GroundTheory.Arith.Etale
theorem _root_.solution (j : T ⟶ U) [IsOpenImmersion j] (N : U.Modules) {O : U.Opens}
    (hO : O ≤ j.opensRange) : Function.Bijective (pullbackUnitApp j N O) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction j)
    (Scheme.Modules.pullbackPushforwardAdjunction j) N
  have h' : ∀ n, pullbackUnitApp j N O n =
      (((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N).app (j ⁻¹ᵁ O))
        (N.presheaf.map (homOfLE (j.image_preimage_le O)).op n) := fun n => by
    rw [pullbackUnitApp, ← h]
    rfl
  have hE : j ''ᵁ (j ⁻¹ᵁ O) = O := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_eq_right.2 hO
  have b1 := ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N).app (j ⁻¹ᵁ O))
  have b2 : Function.Bijective (N.presheaf.map (homOfLE (j.image_preimage_le O)).op) := by
    have : homOfLE (j.image_preimage_le O) = eqToHom hE := Subsingleton.elim _ _
    rw [this]
    exact ConcreteCategory.bijective_of_isIso _
  have e : ⇑(pullbackUnitApp j N O) =
      ⇑(ConcreteCategory.hom (((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N).app
        (j ⁻¹ᵁ O))) ∘ ⇑(ConcreteCategory.hom (N.presheaf.map (homOfLE (j.image_preimage_le O)).op)) :=
    funext h'
  rw [e]
  exact b1.comp b2
end GroundTheory.Arith.Etale
