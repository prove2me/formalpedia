-- Prove2me | solution 1 for HopfAlgebra.exists_finiteFlat_model_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f537d498-0d27-5c99-90e9-7733e9ecff03

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_finiteFlat_model_prod

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

theorem solution
    {R : Type} [CommRing R] {L : Type} [CommRing L] [Algebra R L]
    {Γ : Type} [Group Γ] [MulSemiringAction Γ L] [SMulCommClass Γ R L]
    {M₁ M₂ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [DistribMulAction Γ M₁] [DistribMulAction Γ M₂]
    (H₁ : Type) [CommRing H₁] [HopfAlgebra R H₁] [Module.Finite R H₁] [Module.Flat R H₁]
    [Coalgebra.IsCocomm R H₁]
    (e₁ : WithConv (H₁ →ₐ[R] L) ≃ M₁)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : Γ) (f g : WithConv (H₁ →ₐ[R] L)), (∀ x : H₁, g x = σ • (f x)) → e₁ g = σ • (e₁ f))
    (H₂ : Type) [CommRing H₂] [HopfAlgebra R H₂] [Module.Finite R H₂] [Module.Flat R H₂]
    [Coalgebra.IsCocomm R H₂]
    (e₂ : WithConv (H₂ →ₐ[R] L) ≃ M₂)
    (he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g)
    (he₂_act : ∀ (σ : Γ) (f g : WithConv (H₂ →ₐ[R] L)), (∀ x : H₂, g x = σ • (f x)) → e₂ g = σ • (e₂ f)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ e : WithConv (H →ₐ[R] L) ≃ M₁ × M₂,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : Γ) (f g : WithConv (H →ₐ[R] L)), (∀ x : H, g x = σ • (f x)) → e g = σ • (e f) := by
  classical
  refine ⟨H₁ ⊗[R] H₂, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩

  let fwd : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] L) → M₁ × M₂ := fun F =>
    (e₁ (WithConv.toConv ((WithConv.ofConv F).comp Algebra.TensorProduct.includeLeft)),
      e₂ (WithConv.toConv ((WithConv.ofConv F).comp Algebra.TensorProduct.includeRight)))
  let bwd : M₁ × M₂ → WithConv ((H₁ ⊗[R] H₂) →ₐ[R] L) := fun m =>
    WithConv.toConv (Algebra.TensorProduct.lift (WithConv.ofConv (e₁.symm m.1)) (WithConv.ofConv (e₂.symm m.2))
      (fun _ _ => Commute.all _ _))
  have hfb : ∀ F, bwd (fwd F) = F := by
    intro F
    simp only [fwd, bwd, Equiv.symm_apply_apply, WithConv.ofConv_toConv]
    congr 1
    apply Algebra.TensorProduct.ext'
    intro a b
    rw [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.comp_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hbf : ∀ m, fwd (bwd m) = m := by
    intro m
    simp only [fwd, bwd, WithConv.ofConv_toConv]
    have h1 : (Algebra.TensorProduct.lift (WithConv.ofConv (e₁.symm m.1)) (WithConv.ofConv (e₂.symm m.2))
        (fun _ _ => Commute.all _ _)).comp Algebra.TensorProduct.includeLeft = WithConv.ofConv (e₁.symm m.1) := by
      apply AlgHom.ext; intro a
      simp [Algebra.TensorProduct.lift_tmul]
    have h2 : (Algebra.TensorProduct.lift (WithConv.ofConv (e₁.symm m.1)) (WithConv.ofConv (e₂.symm m.2))
        (fun _ _ => Commute.all _ _)).comp Algebra.TensorProduct.includeRight = WithConv.ofConv (e₂.symm m.2) := by
      apply AlgHom.ext; intro b
      simp [Algebra.TensorProduct.lift_tmul]
    rw [h1, h2, WithConv.toConv_ofConv, WithConv.toConv_ofConv, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  let e : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] L) ≃ M₁ × M₂ := ⟨fwd, bwd, hfb, hbf⟩
  refine ⟨e, ?_, ?_⟩
  ·
    intro F G
    show fwd (F * G) = fwd F + fwd G
    simp only [fwd, Prod.mk_add_mk, ← he₁_add, ← he₂_add]
    congr 1
    · congr 1

      apply congrArg WithConv.toConv ?_ |>.trans (WithConv.toConv_ofConv _)
      apply AlgHom.ext
      intro h
      let 𝓡 := Coalgebra.Repr.arbitrary R h

      let 𝓡' : Coalgebra.Repr R (h ⊗ₜ[R] (1 : H₂)) _ :=
        { index := 𝓡.index
          left := fun i => 𝓡.left i ⊗ₜ 1
          right := fun i => 𝓡.right i ⊗ₜ 1
          eq := by
            rw [TensorProduct.comul_tmul, Bialgebra.comul_one, Algebra.TensorProduct.one_def, ← 𝓡.eq,
              TensorProduct.sum_tmul, map_sum]
            exact Finset.sum_congr rfl fun i _ => by
              simp only [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul] }
      have hL : (F * G).ofConv (h ⊗ₜ (1 : H₂)) =
          ∑ i ∈ 𝓡.index, F.ofConv (𝓡.left i ⊗ₜ 1) * G.ofConv (𝓡.right i ⊗ₜ 1) := by
        have key := AlgHom.toLinearMap_convMul F G
        have := congrArg (fun Lm => (WithConv.ofConv Lm) (h ⊗ₜ[R] (1 : H₂))) key
        simpa [Coalgebra.Repr.convMul_apply 𝓡'] using this
      have hR : (WithConv.toConv ((WithConv.ofConv F).comp Algebra.TensorProduct.includeLeft) *
          WithConv.toConv ((WithConv.ofConv G).comp Algebra.TensorProduct.includeLeft)).ofConv h =
          ∑ i ∈ 𝓡.index, F.ofConv (𝓡.left i ⊗ₜ 1) * G.ofConv (𝓡.right i ⊗ₜ 1) := by
        have key := AlgHom.toLinearMap_convMul
          (WithConv.toConv ((WithConv.ofConv F).comp Algebra.TensorProduct.includeLeft))
          (WithConv.toConv ((WithConv.ofConv G).comp Algebra.TensorProduct.includeLeft))
        have := congrArg (fun Lm => (WithConv.ofConv Lm) h) key
        simpa [Coalgebra.Repr.convMul_apply 𝓡] using this
      show (F * G).ofConv (h ⊗ₜ[R] (1 : H₂)) = _
      rw [hL, hR]
    · congr 1
      apply congrArg WithConv.toConv ?_ |>.trans (WithConv.toConv_ofConv _)
      apply AlgHom.ext
      intro h
      let 𝓡 := Coalgebra.Repr.arbitrary R h
      let 𝓡' : Coalgebra.Repr R ((1 : H₁) ⊗ₜ[R] h) _ :=
        { index := 𝓡.index
          left := fun i => 1 ⊗ₜ 𝓡.left i
          right := fun i => 1 ⊗ₜ 𝓡.right i
          eq := by
            rw [TensorProduct.comul_tmul, Bialgebra.comul_one, Algebra.TensorProduct.one_def, ← 𝓡.eq,
              TensorProduct.tmul_sum, map_sum]
            exact Finset.sum_congr rfl fun i _ => by
              simp only [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul] }
      have hL : (F * G).ofConv ((1 : H₁) ⊗ₜ h) =
          ∑ i ∈ 𝓡.index, F.ofConv (1 ⊗ₜ 𝓡.left i) * G.ofConv (1 ⊗ₜ 𝓡.right i) := by
        have key := AlgHom.toLinearMap_convMul F G
        have := congrArg (fun Lm => (WithConv.ofConv Lm) ((1 : H₁) ⊗ₜ[R] h)) key
        simpa [Coalgebra.Repr.convMul_apply 𝓡'] using this
      have hR : (WithConv.toConv ((WithConv.ofConv F).comp Algebra.TensorProduct.includeRight) *
          WithConv.toConv ((WithConv.ofConv G).comp Algebra.TensorProduct.includeRight)).ofConv h =
          ∑ i ∈ 𝓡.index, F.ofConv (1 ⊗ₜ 𝓡.left i) * G.ofConv (1 ⊗ₜ 𝓡.right i) := by
        have key := AlgHom.toLinearMap_convMul
          (WithConv.toConv ((WithConv.ofConv F).comp Algebra.TensorProduct.includeRight))
          (WithConv.toConv ((WithConv.ofConv G).comp Algebra.TensorProduct.includeRight))
        have := congrArg (fun Lm => (WithConv.ofConv Lm) h) key
        simpa [Coalgebra.Repr.convMul_apply 𝓡] using this
      show (F * G).ofConv ((1 : H₁) ⊗ₜ[R] h) = _
      rw [hL, hR]
  ·
    intro σ F G hFG
    show fwd G = σ • fwd F
    simp only [fwd, Prod.smul_mk]
    congr 1
    · apply he₁_act
      intro x
      exact hFG _
    · apply he₂_act
      intro x
      exact hFG _

end S_HopfAlgebra_exists_finiteFlat_model_prod
end P2MW
export P2MW.S_HopfAlgebra_exists_finiteFlat_model_prod (solution)
