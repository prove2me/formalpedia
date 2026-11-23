-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.isPushout_equalizer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:44.927811+00:00
-- url     : https://prove2.me/submissions/c28837b9-9c11-48c1-86eb-17be90b45f56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction

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
omit hρ
namespace GlobalTheory.AffineQuotient
theorem _root_.solution {T : Type} [CommRing T] [Algebra R T] (α β : B →ₐ[R] T)
    (h₁ : Function.Surjective (productMap β α))
    (h₂ : RingHom.ker (productMap β α) = Ideal.span {z | ∃ b ∈ AlgHom.equalizer α β,
      z = b ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] b}) :
    IsPushout (CommRingCat.ofHom (α.toRingHom.eqLocus β.toRingHom).subtype)
      (CommRingCat.ofHom (α.toRingHom.eqLocus β.toRingHom).subtype)
      (CommRingCat.ofHom α.toRingHom) (CommRingCat.ofHom β.toRingHom) := by
  refine ⟨⟨by ext x; exact x.2⟩, ⟨PushoutCocone.isColimitAux' _ fun s ↦ ?_⟩⟩
  have hs (b : B) (hb : α b = β b) : s.inl b = s.inr b := congr($(s.condition) ⟨b, hb⟩)
  let : Algebra R s.pt := (s.inl.hom.comp (algebraMap R B)).toAlgebra
  let φ : B →ₐ[R] s.pt := ⟨s.inl.hom, fun _ ↦ rfl⟩
  let ψ : B →ₐ[R] s.pt := ⟨s.inr.hom, fun r ↦ (hs _ (by simp)).symm⟩
  have hk : RingHom.ker (productMap β α).toRingHom ≤ RingHom.ker (productMap ψ φ).toRingHom := by
    refine h₂.le.trans (Ideal.span_le.2 ?_)
    rintro _ ⟨b, hb, rfl⟩
    have : ψ b = φ b := (hs b hb).symm
    simpa [sub_eq_zero, RingHom.mem_ker] using this
  let d : T →+* s.pt := (productMap β α).toRingHom.liftOfSurjective h₁
    ⟨(productMap ψ φ).toRingHom, hk⟩
  have hd (z) : d (productMap β α z) = productMap ψ φ z :=
    RingHom.liftOfRightInverse_comp_apply (productMap β α).toRingHom _ _ _ z
  refine ⟨CommRingCat.ofHom d, ?_, ?_, fun {m} hm₁ hm₂ ↦ ?_⟩
  · ext b
    have := hd (1 ⊗ₜ b)
    rw [productMap_right_apply, productMap_right_apply] at this
    exact this
  · ext b
    have := hd (b ⊗ₜ 1)
    rw [productMap_left_apply, productMap_left_apply] at this
    exact this
  · ext t
    obtain ⟨z, rfl⟩ := h₁ t
    refine Eq.trans ?_ (hd z).symm
    have e₁ (b) : m.hom (α b) = φ b := congr($hm₁ b)
    have e₂ (b) : m.hom (β b) = ψ b := congr($hm₂ b)
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      rw [productMap_apply_tmul, productMap_apply_tmul, ← e₁, ← e₂]
      exact map_mul m.hom _ _
end GlobalTheory.AffineQuotient
