-- Prove2me | solution 1 for MazurTransfer.finite_field_extension_points_of_finite_scheme
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-11T00:31:38.144233+00:00
-- url     : https://prove2.me/submissions/7ccb43d5-5558-4b8d-b9f7-9a90581b5d8a

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a scheme finite over a field has finitely many points
over every extension field, by injection into coordinate algebra maps.
Named downstream consumer: finite actual norm kernel Galois modules.
-/
import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

noncomputable section
namespace MazurTransfer.PublicFiniteSchemePointCardinality
open CategoryTheory AlgebraicGeometry NeronModelInfra
variable (F K : Type) [Field F] [Field K] [Algebra F K]

theorem finite_points (X : Scheme.{0}) (t : X ⟶ Spec (CommRingCat.of F)) [IsFinite t] :
    Finite (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F K))) t) := by
  letI : IsAffine X := isAffine_of_isAffineHom t
  let A : CommRingCat := Γ(X, ⊤)
  let α : CommRingCat.of F ⟶ A := Spec.preimage (X.isoSpec.inv ≫ t)
  have hα : Spec.map α = X.isoSpec.inv ≫ t := Spec.map_preimage _
  have hαfinite : α.hom.Finite := by
    apply (IsFinite.SpecMap_iff α).mp
    rw [hα]
    infer_instance
  letI : Algebra F A := α.hom.toAlgebra
  letI : Module.Finite F A := hαfinite
  let encode (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F K))) t) :
      A →ₐ[F] K := by
    let θ : A ⟶ CommRingCat.of K := Spec.preimage (x.val ≫ X.isoSpec.hom)
    have hθ : Spec.map θ = x.val ≫ X.isoSpec.hom := Spec.map_preimage _
    have hαθ : α ≫ θ = CommRingCat.ofHom (algebraMap F K) := by
      apply Spec.map_inj.mp
      simp only [Spec.map_comp, hα, hθ, Category.assoc, Iso.hom_inv_id_assoc]
      exact x.property
    exact { θ.hom with
      commutes' r := congrArg (fun ψ : CommRingCat.of F ⟶ CommRingCat.of K => ψ.hom r) hαθ }
  have hinj : Function.Injective encode := by
    intro x y h
    apply Subtype.ext
    apply (cancel_mono X.isoSpec.hom).mp
    have hθ : Spec.preimage (x.val ≫ X.isoSpec.hom) =
        Spec.preimage (y.val ≫ X.isoSpec.hom) := by
      ext a
      exact AlgHom.congr_fun h a
    have hm := congrArg Spec.map hθ
    simpa only [Spec.map_preimage] using hm
  exact Finite.of_injective encode hinj

end MazurTransfer.PublicFiniteSchemePointCardinality
#print axioms MazurTransfer.PublicFiniteSchemePointCardinality.finite_points

open CategoryTheory AlgebraicGeometry NeronModelInfra
theorem solution
    (F K : Type) [Field F] [Field K] [Algebra F K]
    (X : Scheme.{0}) (t : X ⟶ Spec (CommRingCat.of F)) [IsFinite t] :
    Finite (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F K))) t) := by
  exact MazurTransfer.PublicFiniteSchemePointCardinality.finite_points F K X t

#print axioms solution
