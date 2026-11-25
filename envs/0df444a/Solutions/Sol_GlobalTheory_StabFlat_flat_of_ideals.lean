-- Prove2me | solution 1 for GlobalTheory.StabFlat.flat_of_ideals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:19:44.678495+00:00
-- url     : https://prove2.me/submissions/3029340a-4fed-4adb-b43e-1fbd7e1bf8cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocalizationOfIsStandardSmooth
import Theorems.Thm_GlobalTheory_StabFlat_flat_of_regular

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
theorem _root_.solution : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (X H : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (j : H ⟶ X), IsClosedImmersion j → (∀ (h : H) (σ : V →+* X.presheaf.stalk (j h)), X.fromSpecStalk (j h) ≫ f = Spec.map (CommRingCat.ofHom σ) → ¬ IsUnit (σ ϖ) → ∃ I : Ideal (X.presheaf.stalk (j h)), IsSMulRegular (X.presheaf.stalk (j h) ⧸ I) (σ ϖ) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : X.presheaf.stalk (j h) →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ H, y ≫ j = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (j h)) ↔ I ≤ RingHom.ker φ) → Flat (j ≫ f) := by
  intro V _ _ _ ϖ hϖ X H f j hj hI
  refine Flat.of_stalkMap _ fun h => ?_
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (X.fromSpecStalk (j h) ≫ f)
  have reg : IsSMulRegular (H.presheaf.stalk h) ((j.stalkMap h).hom (σ.hom ϖ)) := by
    by_cases hu : IsUnit (σ.hom ϖ)
    · exact (hu.map _).isRegular.left.isSMulRegular
    obtain ⟨I, hr, hI⟩ := hI h σ.hom hσ.symm hu
    have h₁ : I ≤ RingHom.ker (j.stalkMap h).hom :=
      (hI (H.presheaf.stalk h) (j.stalkMap h).hom).1
        ⟨H.fromSpecStalk h, (Scheme.SpecMap_stalkMap_fromSpecStalk j).symm⟩
    have : Nontrivial (X.presheaf.stalk (j h) ⧸ I) := Ideal.Quotient.nontrivial_iff.2
      (ne_top_of_le_ne_top (RingHom.ker_ne_top _) h₁)
    have : IsLocalRing (X.presheaf.stalk (j h) ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    obtain ⟨y, hy⟩ := (hI (X.presheaf.stalk (j h) ⧸ I) (Ideal.Quotient.mk I)).2 Ideal.mk_ker.ge
    have hl : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have e : y (IsLocalRing.closedPoint _) = h := by
      apply j.isClosedEmbedding.injective
      refine (congrArg (fun q => q (IsLocalRing.closedPoint _)) hy).trans ?_
      exact (congrArg (X.fromSpecStalk (j h)) (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk I))).trans
        Scheme.fromSpecStalk_closedPoint
    let ψ := H.presheaf.stalkSpecializes (specializes_of_eq e) ≫ Scheme.stalkClosedPointTo y
    have hψ : j.stalkMap h ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      apply Spec.map_injective
      rw [← cancel_mono (X.fromSpecStalk (j h)), ← hy, Spec.map_comp, Category.assoc,
        Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc,
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]
    have hψ' : ∀ a, ψ.hom ((j.stalkMap h).hom a) = Ideal.Quotient.mk I a := fun a => congrArg (fun q => q.hom a) hψ
    refine IsSMulRegular.of_right_eq_zero_of_smul fun b hb => ?_
    obtain ⟨a, rfl⟩ := j.stalkMap_surjective h b
    refine h₁ (Ideal.Quotient.eq_zero_iff_mem.1 (hr.right_eq_zero_of_smul ?_))
    have := congrArg ψ.hom hb
    rw [smul_eq_mul, map_mul, hψ', hψ', map_zero] at this
    exact this
  have fl : (σ ≫ j.stalkMap h).hom.Flat := flat_of_regular hϖ _ reg
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
