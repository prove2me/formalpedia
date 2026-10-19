-- Prove2me | solution 1 for MazurTransfer.FiniteSchemeGeometricPointOpenStabilizer.stabilizer_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T23:19:33.176279+00:00
-- url     : https://prove2.me/submissions/e5f7e79a-c935-43ba-8fea-bab7628067ec

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a point of a scheme finite over a field has an open
Galois stabilizer in an algebraic extension, using finite affine
coordinates. Named downstream consumer: actual norm fibres and kernels.
-/
import Theorems.Thm_MazurTransfer_FiniteTypeGaloisAlgHomOpenStabilizer_stabilizer_isOpen
noncomputable section
open CategoryTheory AlgebraicGeometry
theorem solution (F K : Type) [Field F] [Field K] [Algebra F K] [Algebra.IsIntegral F K] (X : Scheme.{0}) (t : X ⟶ Spec (CommRingCat.of F)) [IsFinite t]
    (q : Spec (CommRingCat.of K) ⟶ X)
    (hq : q ≫ t = Spec.map (CommRingCat.ofHom (algebraMap F K))) :
    IsOpen {σ : K ≃ₐ[F] K | Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ q = q} := by
  letI : IsAffine X := isAffine_of_isAffineHom t
  let A : CommRingCat := Γ(X, ⊤)
  let α : CommRingCat.of F ⟶ A := Spec.preimage (X.isoSpec.inv ≫ t)
  let θ : A ⟶ CommRingCat.of K := Spec.preimage (q ≫ X.isoSpec.hom)
  have hα : Spec.map α = X.isoSpec.inv ≫ t := Spec.map_preimage _
  have hθ : Spec.map θ = q ≫ X.isoSpec.hom := Spec.map_preimage _
  have hαfinite : α.hom.Finite := by
    apply (IsFinite.SpecMap_iff α).mp
    rw [hα]
    infer_instance
  letI : Algebra F A := α.hom.toAlgebra
  letI : Module.Finite F A := hαfinite
  have hαθ : α ≫ θ = CommRingCat.ofHom (algebraMap F K) := by
    apply Spec.map_inj.mp
    simp only [Spec.map_comp, hα, hθ, Category.assoc, Iso.hom_inv_id_assoc]
    exact hq
  let f : A →ₐ[F] K :=
    { θ.hom with
      commutes' r := congrArg (fun ψ : CommRingCat.of F ⟶ CommRingCat.of K => ψ.hom r) hαθ }
  have hset : {σ : K ≃ₐ[F] K | Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ q = q} =
      {σ : K ≃ₐ[F] K | σ.toAlgHom.comp f = f} := by
    ext σ
    simp only [Set.mem_setOf_eq]
    have hspec :
        (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ q = q) ↔
          θ ≫ CommRingCat.ofHom σ.toRingHom = θ := by
      rw [← cancel_mono X.isoSpec.hom, Category.assoc, ← hθ, ← Spec.map_comp]
      exact Spec.map_inj
    rw [hspec]
    constructor
    · intro h
      ext r
      exact congrArg (fun ψ : A ⟶ CommRingCat.of K => ψ.hom r) h
    · intro h
      ext r
      exact AlgHom.congr_fun h r
  rw [hset]
  exact MazurTransfer.FiniteTypeGaloisAlgHomOpenStabilizer.stabilizer_isOpen F K A f

#print axioms solution
