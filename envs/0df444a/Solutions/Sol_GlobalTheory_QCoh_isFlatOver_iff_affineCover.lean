-- Prove2me | solution 1 for GlobalTheory.QCoh.isFlatOver_iff_affineCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:12:41.7266+00:00
-- url     : https://prove2.me/submissions/f2b42e06-939c-41b6-9c96-1fb7abb71702

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds

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
theorem _root_.solution [F.IsQuasicoherent] {ι : Type*} (𝒰 : ι → X.Opens)
    (hcov : IsOpenCover 𝒰) (haff : ∀ i, IsAffineOpen (𝒰 i)) :
    IsFlatOver F ρ ↔ ∀ i,
      letI := baseModule F (𝒰 i) ρ
      Module.Flat R Γ(F, 𝒰 i) :=
  ⟨fun h i ↦ h _ (haff i), fun h ↦ .of_forall_exists_affine fun x ↦
    have ⟨i, hi⟩ := hcov.exists_mem x
    ⟨𝒰 i, haff i, hi, h i⟩⟩
end GlobalTheory.QCoh
