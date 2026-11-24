-- Prove2me | solution 1 for GlobalTheory.FibSurj.fibMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:45:31.369872+00:00
-- url     : https://prove2.me/submissions/969105f6-c0b2-4320-9805-0b04fb4cb34e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SpecialFibreUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecialFibreConnectedOfBaseChange
import Theorems.Thm_GlobalTheory_FibSurj_fibMap_isPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.FibSurj
open IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O) [IsLocalHom φ]
  {X : Scheme.{0}} (s : X ⟶ Spec (.of V))
namespace GlobalTheory.FibSurj
theorem _root_.solution : Surjective (fibMap φ s) := by
  have hψ : Surjective (Spec.map (CommRingCat.ofHom (ResidueField.map φ))) := by
    constructor
    intro x
    obtain ⟨y⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of (ResidueField O))))
    exact ⟨y, Subsingleton.elim _ _⟩
  exact MorphismProperty.of_isPullback (fibMap_isPullback φ s).flip hψ
end GlobalTheory.FibSurj
