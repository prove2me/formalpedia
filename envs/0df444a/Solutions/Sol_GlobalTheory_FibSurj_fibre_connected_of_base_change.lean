-- Prove2me | solution 1 for GlobalTheory.FibSurj.fibre_connected_of_base_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:07:15.662706+00:00
-- url     : https://prove2.me/submissions/350d2873-a0c4-4463-838b-04573804403e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SpecialFibreUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecialFibreConnectedOfBaseChange
import Theorems.Thm_GlobalTheory_FibSurj_fibMap_surjective

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
namespace GlobalTheory.FibSurj
theorem _root_.solution :
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O), IsLocalHom φ → ∀ (X : Scheme.{0}) (s : X ⟶ Spec (.of V)), ConnectedSpace ↑(GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre (pullback.snd s (Spec.map (CommRingCat.ofHom φ)))) → ConnectedSpace ↑(GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre s) := by
  intro V _ _ _ O _ _ _ φ hφ X s hc
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre at hc ⊢
  exact (fibMap_surjective φ s).surj.connectedSpace (fibMap φ s).continuous
end GlobalTheory.FibSurj
