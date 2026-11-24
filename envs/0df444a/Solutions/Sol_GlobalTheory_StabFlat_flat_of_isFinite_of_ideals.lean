-- Prove2me | solution 1 for GlobalTheory.StabFlat.flat_of_isFinite_of_ideals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:29:07.36707+00:00
-- url     : https://prove2.me/submissions/63b752c2-a619-4ab8-9a37-1b69ac847745

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatClosedSubschemeFiniteOverLocalRing
import Theorems.Thm_GlobalTheory_StabFlat_eq_ker_stalkMap_of_points
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_UnramifiedEndFlat_flat_stalkMap_of_specializes


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.StabFlat
namespace GlobalTheory.StabFlat
theorem _root_.solution : ∀ (V : Type) [CommRing V] [IsLocalRing V] (X H : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (j : H ⟶ X), IsClosedImmersion j → IsFinite (j ≫ f) → (∀ (h : H) (σ : V →+* X.presheaf.stalk (j h)), X.fromSpecStalk (j h) ≫ f = Spec.map (CommRingCat.ofHom σ) → IsLocalHom σ → ∃ I : Ideal (X.presheaf.stalk (j h)), ((Ideal.Quotient.mk I).comp σ).Flat ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : X.presheaf.stalk (j h) →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ H, y ≫ j = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (j h)) ↔ I ≤ RingHom.ker φ) → Flat (j ≫ f) := by
  intro V _ _ X H f j hj hfin hI
  refine Flat.of_stalkMap _ fun h' => ?_
  obtain ⟨h, hh, hc⟩ : ∃ h : H, h' ⤳ h ∧ (j ≫ f) h = IsLocalRing.closedPoint V := by
    have hcl : IsClosed ((j ≫ f) '' closure {h'}) := (j ≫ f).isClosedMap _ isClosed_closure
    have hm : IsLocalRing.closedPoint V ∈ (j ≫ f) '' closure {h'} :=
      (IsLocalRing.specializes_closedPoint ((j ≫ f) h')).mem_closed hcl ⟨h', subset_closure rfl, rfl⟩
    obtain ⟨h, hh, e⟩ := hm
    exact ⟨h, specializes_iff_mem_closure.2 hh, e⟩
  refine UnramifiedEndFlat.flat_stalkMap_of_specializes _ hh ?_
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (X.fromSpecStalk (j h) ≫ f)
  have hloc : IsLocalHom σ.hom := by
    refine (IsLocalRing.isLocalHom_iff_comap_closedPoint σ.hom).2 ?_
    refine (congrArg (fun q => q (IsLocalRing.closedPoint _)) hσ).trans ?_
    exact (congrArg f Scheme.fromSpecStalk_closedPoint).trans hc
  obtain ⟨I, hr, hI⟩ := hI h σ.hom hσ.symm hloc
  obtain rfl := eq_ker_stalkMap_of_points j h I hI
  have fl : (σ ≫ j.stalkMap h).hom.Flat :=
    hr.comp (RingHom.Flat.of_bijective
      (f := (RingHom.quotientKerEquivOfSurjective (j.stalkMap_surjective h)).toRingHom)
      (RingHom.quotientKerEquivOfSurjective (j.stalkMap_surjective h)).bijective)
  have e : σ ≫ j.stalkMap h = StructureSheaf.toStalk V ((j ≫ f) h) ≫ (j ≫ f).stalkMap h := by
    apply Spec.map_injective
    refine Eq.trans ?_ (Spec.map_comp _ _).symm
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (Spec.fromSpecStalk_eq' (CommRingCat.of V) ((j ≫ f) h)))
    rw [Spec.map_comp, hσ, Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]
    exact (Scheme.SpecMap_stalkMap_fromSpecStalk (j ≫ f)).symm
  let S := (Spec (CommRingCat.of V)).presheaf.stalk ((j ≫ f) h)
  letI : Algebra V S := StructureSheaf.stalkAlgebra V ((j ≫ f) h)
  have : ((j ≫ f) h).asIdeal.IsPrime := PrimeSpectrum.isPrime (R := V) _
  have : IsLocalization.AtPrime S ((j ≫ f) h).asIdeal := StructureSheaf.IsLocalization.to_stalk V _
  letI : Algebra V (H.presheaf.stalk h) := (σ ≫ j.stalkMap h).hom.toAlgebra
  letI : Algebra S (H.presheaf.stalk h) := ((j ≫ f).stalkMap h).hom.toAlgebra
  have : IsScalarTower V S (H.presheaf.stalk h) := IsScalarTower.of_algebraMap_eq' (congrArg (·.hom) e)
  exact (Module.flat_iff_of_isLocalization S ((j ≫ f) h).asIdeal.primeCompl (H.presheaf.stalk h)).2 fl
end GlobalTheory.StabFlat
