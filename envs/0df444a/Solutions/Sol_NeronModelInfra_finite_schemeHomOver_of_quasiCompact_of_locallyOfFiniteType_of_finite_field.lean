-- Prove2me | solution 1 for NeronModelInfra.finite_schemeHomOver_of_quasiCompact_of_locallyOfFiniteType_of_finite_field
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-16T19:21:31.607348+00:00
-- url     : https://prove2.me/submissions/9b7ff862-7891-4172-b06d-65792cab8e14

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: standalone platform proof of finite residue points;
named downstream consumer: the original Picard formal subgroup. -/
import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
universe u
/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: finiteness of algebra-valued points of a finite-type affine
scheme over a finite target ring. Named downstream consumer:
FiniteTypeSchemeFiniteFieldPoints and the original Picard special fibre. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
namespace MazurTransfer.FiniteTypeAlgebraHomPoints

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

theorem finite_algHom [Algebra.FiniteType R A] [Finite B] : Finite (A →ₐ[R] B) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  exact Finite.of_injective (fun f : A →ₐ[R] B => fun x : s => f x)
    (fun f g h => AlgHom.ext_of_adjoin_eq_top hs (fun x hx => congrFun h ⟨x, hx⟩))

def affinePointToAlgHom
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))) : A →ₐ[R] B := by
  let g : CommRingCat.of A ⟶ CommRingCat.of B := (Spec.fullyFaithful.preimage x.1).unop
  have hg : Spec.map g = x.1 := Spec.fullyFaithful.map_preimage x.1
  have hcomp : CommRingCat.ofHom (algebraMap R A) ≫ g = CommRingCat.ofHom (algebraMap R B) :=
    Spec.map_injective ((Spec.map_comp _ _).trans
      ((congrArg (fun h => h ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))) hg).trans x.2))
  exact {
    toRingHom := g.hom
    commutes' := fun r => congrArg (fun f : CommRingCat.of R ⟶ CommRingCat.of B => f.hom r) hcomp }

theorem affinePointToAlgHom_spec
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
    Spec.map (CommRingCat.ofHom (affinePointToAlgHom R A B x).toRingHom) = x.1 := by
  change Spec.map (Spec.fullyFaithful.preimage x.1).unop = x.1
  exact Spec.fullyFaithful.map_preimage x.1

theorem finite_affine_spectrum_points [Algebra.FiniteType R A] [Finite B] :
    Finite (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))) := by
  letI := finite_algHom R A B
  apply Finite.of_injective (affinePointToAlgHom R A B)
  intro x y h
  apply Subtype.ext
  exact (affinePointToAlgHom_spec R A B x).symm.trans
    ((congrArg (fun f : A →ₐ[R] B => Spec.map (CommRingCat.ofHom f.toRingHom)) h).trans
      (affinePointToAlgHom_spec R A B y))

end MazurTransfer.FiniteTypeAlgebraHomPoints
/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: finite residue-field points of a quasi-compact locally
finite-type scheme. Named downstream consumer: finite index of the original
Picard Néron model's formal reduction kernel. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
namespace MazurTransfer.FiniteTypeSchemeFiniteFieldPoints

variable (R κ : Type u) [CommRing R] [Field κ] [Finite κ] [Algebra R κ]

theorem finite_affine_points (Y : Scheme.{u}) [IsAffine Y]
    (f : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    Finite (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R κ))) f) := by
  let A := Γ(Y, ⊤)
  let φ : CommRingCat.of R ⟶ A :=
    (Spec.fullyFaithful.preimage (Y.isoSpec.inv ≫ f)).unop
  have hφ : Spec.map φ = Y.isoSpec.inv ≫ f := Spec.fullyFaithful.map_preimage _
  letI : Algebra R A := φ.hom.toAlgebra
  haveI : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
  haveI : Algebra.FiniteType R A := HasRingHomProperty.Spec_iff.mp ‹LocallyOfFiniteType (Spec.map φ)›
  letI := FiniteTypeAlgebraHomPoints.finite_affine_spectrum_points R A κ
  let F : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R κ))) f →
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R κ))) (Spec.map φ) :=
    fun x => ⟨x.1 ≫ Y.isoSpec.hom, by
      rw [hφ, Category.assoc, Iso.hom_inv_id_assoc]
      exact x.2⟩
  apply Finite.of_injective F
  intro x y h
  apply Subtype.ext
  exact (cancel_mono Y.isoSpec.hom).mp (congrArg Subtype.val h)

theorem finite_points (Y : Scheme.{u})
    (f : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f] :
    Finite (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R κ))) f) := by
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := Y.affineCover.finiteSubcover
  let t := Spec.map (CommRingCat.ofHom (algebraMap R κ))
  letI (i : 𝒰.I₀) : Finite (SchemeHomOver t (𝒰.f i ≫ f)) :=
    finite_affine_points R κ (𝒰.X i) (𝒰.f i ≫ f)
  let F : (Σ i : 𝒰.I₀, SchemeHomOver t (𝒰.f i ≫ f)) → SchemeHomOver t f :=
    fun x => ⟨x.2.1 ≫ 𝒰.f x.1, (Category.assoc _ _ _).trans x.2.2⟩
  apply Finite.of_surjective F
  intro y
  let k₀ : Spec (CommRingCat.of κ) := IsLocalRing.closedPoint κ
  obtain ⟨i, z, hz⟩ := 𝒰.exists_eq (y.1.base k₀)
  have hRange : Set.range y.1.base ⊆ Set.range (𝒰.f i).base := by
    rintro _ ⟨p, rfl⟩
    have hp : p = k₀ := Subsingleton.elim _ _
    exact ⟨z, hz.trans (congrArg y.1.base hp).symm⟩
  let l := IsOpenImmersion.lift (𝒰.f i) y.1 hRange
  have hl : l ≫ 𝒰.f i = y.1 := IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨i, ⟨l, ?_⟩⟩, ?_⟩
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun h => h ≫ f) hl).trans y.2)
  · exact Subtype.ext hl

end MazurTransfer.FiniteTypeSchemeFiniteFieldPoints
theorem solution (R κ : Type u) [CommRing R] [Field κ] [Finite κ] [Algebra R κ]
    (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] [QuasiCompact f] :
    Finite (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R κ))) f) :=
  MazurTransfer.FiniteTypeSchemeFiniteFieldPoints.finite_points R κ Y f
#print axioms solution
