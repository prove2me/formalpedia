-- Prove2me | solution 1 for GlobalTheory.QCoh.isFlatOver_structureModule_iff_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:06:17.231638+00:00
-- url     : https://prove2.me/submissions/b78acc82-624e-40df-8273-cd031febdf37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_isFlatOver_structureModule_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
variable {R : Type*} [CommRing R] (ρ : R →+* Γ(X, ⊤))
variable {ρ}
namespace GlobalTheory.QCoh
theorem _root_.solution {R : CommRingCat.{u}} (f : X ⟶ Spec R) :
    IsFlatOver (structureModule X) (structureRingHom f) ↔ Flat f := by
  rw [isFlatOver_structureModule_iff, HasRingHomProperty.iff_of_iSup_eq_top (P := @Flat)
    (fun U : X.affineOpens ↦ U) (iSup_affineOpens_eq_top X)]
  have key (U : X.Opens) : (baseHom U (structureRingHom f)).Flat ↔
      (f.appLE ⊤ U le_top).hom.Flat :=
    RingHom.Flat.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso R).inv (f.appLE ⊤ U le_top)
  exact ⟨fun h U ↦ (key U).1 (h U U.2), fun h U hU ↦ (key U).2 (h ⟨U, hU⟩)⟩
end GlobalTheory.QCoh
