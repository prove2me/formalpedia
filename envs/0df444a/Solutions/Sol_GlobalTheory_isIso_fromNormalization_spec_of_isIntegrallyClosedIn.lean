-- Prove2me | solution 1 for GlobalTheory.isIso_fromNormalization_spec_of_isIntegrallyClosedIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:03:38.115958+00:00
-- url     : https://prove2.me/submissions/5db57982-473b-4c2a-a431-ecb70134e5aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueLiftSpecOfIsLocalizationAway

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R R' : Type u) [CommRing R]
    [CommRing R'] [Algebra R R'] [IsIntegrallyClosedIn R R'] :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap R R'))).fromNormalization := by
  set f := Spec.map (CommRingCat.ofHom (algebraMap R R')) with hf
  have : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  rw [← MorphismProperty.isomorphisms.iff, (MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (arrowIsoSpecΓOfIsAffine _), MorphismProperty.isomorphisms.iff]
  suffices h : IsIso (f.fromNormalization.app ⊤) by
    have : IsIso f.fromNormalization.appTop := h
    infer_instance
  rw [f.fromNormalization_app (isAffineOpen_top (Spec (.of R)))]
  let _ := (f.app ⊤).hom.toAlgebra
  let eR := Scheme.ΓSpecIso (.of R)
  let eR' : Γ(Spec (.of R'), f ⁻¹ᵁ ⊤) ≅ CommRingCat.of R' := Scheme.ΓSpecIso (.of R')
  have hnat : ∀ x, eR'.hom (algebraMap Γ(Spec (.of R), ⊤) Γ(Spec (.of R'), f ⁻¹ᵁ ⊤) x) =
      algebraMap R R' (eR.hom x) := fun x =>
    congrArg (fun g => g.hom x) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R R')))
  have hinj : ∀ y, eR'.inv (eR'.hom y) = y := fun y => eR'.hom_inv_id_apply y
  have hic : IsIntegrallyClosedIn Γ(Spec (.of R), ⊤) Γ(Spec (.of R'), f ⁻¹ᵁ ⊤) := by
    rw [isIntegrallyClosedIn_iff]
    refine ⟨fun x y hxy => ?_, fun {x} hx => ?_⟩
    · have h1 := congrArg eR'.hom hxy
      rw [hnat, hnat] at h1
      have h2 := IsIntegralClosure.algebraMap_injective R R R' h1
      simpa using congrArg eR.inv h2
    · have hx' : IsIntegral R (eR'.hom.hom x) :=
        IsIntegral.map_of_comp_eq eR.hom.hom eR'.hom.hom
          (RingHom.ext fun z => (hnat z).symm) hx
      obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := R)).mp hx'
      refine ⟨eR.inv y, ?_⟩
      rw [← hinj (algebraMap _ _ (eR.inv y)), ← hinj x, hnat, Iso.inv_hom_id_apply]
      exact congrArg (fun z => eR'.inv z) hy
  have hbij : Function.Bijective (algebraMap Γ(Spec (.of R), ⊤)
      (integralClosure Γ(Spec (.of R), ⊤) Γ(Spec (.of R'), f ⁻¹ᵁ ⊤))) := by
    refine ⟨fun x y hxy => IsIntegralClosure.algebraMap_injective _ Γ(Spec (.of R), ⊤) _
      (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := (IsIntegralClosure.isIntegral_iff (A := Γ(Spec (.of R), ⊤))).mp hz
    exact ⟨y, rfl⟩
  have : IsIso (CommRingCat.ofHom (algebraMap Γ(Spec (.of R), ⊤)
      (integralClosure Γ(Spec (.of R), ⊤) Γ(Spec (.of R'), f ⁻¹ᵁ ⊤)))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  infer_instance
end GlobalTheory
