-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.coaction_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:56:33.411509+00:00
-- url     : https://prove2.me/submissions/15199d0f-c68a-437e-a2a7-dac80ac7de95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
import Theorems.Thm_GlobalTheory_AffineQuotient_specHom_injective
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
theorem _root_.solution [Mono i] [Module.Finite R Λ] :
    Function.Surjective (productMap (includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ) := by
  let m := productMap (includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ
  have : Epi (CommRingCat.ofHom m.toRingHom) := by
    refine ⟨fun {T} φ ψ h ↦ ?_⟩
    have hm (z) : φ (m z) = ψ (m z) := congr($h z)
    let : Algebra R T := (φ.hom.comp (algebraMap R (B ⊗[R] Λ))).toAlgebra
    let φ' : B ⊗[R] Λ →ₐ[R] T := ⟨φ.hom, fun _ ↦ rfl⟩
    let ψ' : B ⊗[R] Λ →ₐ[R] T := ⟨ψ.hom, fun r ↦ by
      have := hm (algebraMap R _ r)
      rw [AlgHom.commutes] at this
      exact this.symm⟩
    have h₁ : φ'.comp includeLeft = ψ'.comp (includeLeft : B →ₐ[R] B ⊗[R] Λ) := by
      ext b
      have := hm (b ⊗ₜ 1)
      rw [productMap_left_apply] at this
      exact this
    have h₂ : φ'.comp ρ = ψ'.comp ρ := by
      ext b
      have := hm (1 ⊗ₜ b)
      rw [productMap_right_apply] at this
      exact this
    have h₃ := specHom_comp_coaction i v ρ hρ φ'
    rw [h₂, h₁, specHom_comp_coaction i v ρ hρ ψ', mul_left_inj, cancel_mono] at h₃
    have h₄ := specHom_injective h₃
    have : φ' = ψ' := Algebra.TensorProduct.ext h₁ h₄.symm
    ext1
    exact congr(($this).toRingHom)
  refine RingHom.surjective_of_epi_of_finite (CommRingCat.ofHom m.toRingHom) ?_
  refine RingHom.Finite.of_comp_finite
    (f := (includeLeftRingHom : B →+* B ⊗[R] B)) ?_
  have : (CommRingCat.ofHom m.toRingHom).hom.comp (includeLeftRingHom : B →+* B ⊗[R] B) =
      algebraMap B (B ⊗[R] Λ) := by
    ext b
    simp [m]
  rw [this, RingHom.finite_algebraMap]
  infer_instance
end GlobalTheory.AffineQuotient
