-- Prove2me | solution 1 for GlobalTheory.LocalRingGeneralisation.isIso_stalkMap_fromSpecStalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:08:28.945102+00:00
-- url     : https://prove2.me/submissions/006aaddb-902d-4f88-8a8f-d31716687e4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_StalkGenerizationGermCompat
import Theorems.Thm_GlobalTheory_LocalRingGeneralisation_flat_fromSpecStalk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open GlobalTheory GlobalTheory.LocalRingGeneralisation
namespace GlobalTheory.LocalRingGeneralisation
theorem _root_.solution (X : Scheme.{0}) (x : X) (y : Spec (X.presheaf.stalk x)) :
    IsIso ((X.fromSpecStalk x).stalkMap y) := by
  have := flat_fromSpecStalk X x
  have hs : SurjectiveOnStalks (X.fromSpecStalk x) := inferInstance
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, (X.fromSpecStalk x).stalkMap_surjective y⟩
  have hl : IsLocalHom ((X.fromSpecStalk x).stalkMap y).hom := inferInstance
  have h := Flat.stalkMap (X.fromSpecStalk x) y
  algebraize [((X.fromSpecStalk x).stalkMap y).hom]
  have : IsLocalHom (algebraMap (X.presheaf.stalk ((X.fromSpecStalk x) y))
    ((Spec (X.presheaf.stalk x)).presheaf.stalk y)) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := X.presheaf.stalk ((X.fromSpecStalk x) y)) (B := (Spec (X.presheaf.stalk x)).presheaf.stalk y)
  exact FaithfulSMul.algebraMap_injective _ _
end GlobalTheory.LocalRingGeneralisation
