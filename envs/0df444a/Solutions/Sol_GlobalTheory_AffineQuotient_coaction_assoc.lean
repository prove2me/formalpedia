-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.coaction_assoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:56:31.03681+00:00
-- url     : https://prove2.me/submissions/ff1ddae9-fe3a-4d5c-8c8a-445de7e5f8de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
import Theorems.Thm_GlobalTheory_AffineQuotient_specHom_injective
import Theorems.Thm_GlobalTheory_AffineQuotient_specHom_lift_comul
import Theorems.Thm_GlobalTheory_AffineQuotient_specHom_comp_coaction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open TensorProduct Algebra.TensorProduct
open GlobalTheory GlobalTheory.AffineQuotient
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R]
variable {Λ B : Type} [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]
variable {A : Over (Spec (CommRingCat.of R))} [GrpObj A]
  (i : specOver R Λ ⟶ A) (v : specOver R B ⟶ A) (ρ : B →ₐ[R] B ⊗[R] Λ)
  (hρ : specHom ρ ≫ v = (specHom includeRight ≫ i) * (specHom includeLeft ≫ v))
include hρ
namespace GlobalTheory.AffineQuotient
theorem _root_.solution [IsCommMonObj A] [IsMonHom i] [Mono v] (b : B) :
    TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) =
      (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b) := by
  let l : B →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) := includeLeft
  let r₁ : Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) := includeRight.comp includeLeft
  let r₂ : Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) := includeRight.comp includeRight
  let φ₀ : B ⊗[R] Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) := Algebra.TensorProduct.lift l r₁ fun _ _ ↦ .all _ _
  let φ₁ : B ⊗[R] Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) :=
    Algebra.TensorProduct.lift (φ₀.comp ρ) r₂ fun _ _ ↦ .all _ _
  let φ₂ : B ⊗[R] Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) :=
    Algebra.TensorProduct.lift l ((Algebra.TensorProduct.lift r₁ r₂ fun _ _ ↦ .all _ _).comp
      (Bialgebra.comulAlgHom R Λ)) fun _ _ ↦ .all _ _
  have h₀ := specHom_comp_coaction i v ρ hρ φ₀
  have h₁ := specHom_comp_coaction i v ρ hρ φ₁
  have h₂ := specHom_comp_coaction i v ρ hρ φ₂
  rw [lift_comp_includeRight', lift_comp_includeLeft] at h₀ h₁ h₂
  rw [h₀, ← _root_.mul_assoc, _root_.mul_comm (specHom r₂ ≫ i), ← MonObj.mul_comp] at h₁
  rw [specHom_lift_comul, ← h₁, cancel_mono] at h₂
  have h : φ₂ (ρ b) = φ₁ (ρ b) := congr($(specHom_injective h₂) b)
  have e₁ (z : B ⊗[R] Λ) :
      TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ z) = φ₁ z := by
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, φ₁,
        Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply]
      generalize ρ x = w
      induction w with
      | zero => simp
      | add x y hx hy => simp only [map_add, add_tmul, add_mul, hx, hy]
      | tmul x y => simp [φ₀, l, r₁, r₂]
  have e₂ (z : B ⊗[R] Λ) : (Coalgebra.comul (R := R) (A := Λ)).lTensor B z = φ₂ z := by
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      simp only [LinearMap.lTensor_tmul, φ₂, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
        Bialgebra.comulAlgHom_apply]
      generalize Coalgebra.comul (R := R) y = w
      induction w with
      | zero => simp
      | add x y hx hy => simp only [map_add, tmul_add, mul_add, hx, hy]
      | tmul x y => simp [l, r₁, r₂]
  rw [e₁, e₂, h]
end GlobalTheory.AffineQuotient
