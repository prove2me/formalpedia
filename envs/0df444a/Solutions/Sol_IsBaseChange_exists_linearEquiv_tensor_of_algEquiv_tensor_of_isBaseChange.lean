-- Prove2me | solution 1 for IsBaseChange.exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/5e1ed5c5-a921-5546-95a2-ce22e628d30e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsBaseChange_exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem solution
    {R₀ : Type u} [CommRing R₀] {R : Type u} [CommRing R] [Algebra R₀ R]
    {Γ₀ : Type u} [CommRing Γ₀] [Algebra R₀ Γ₀]
    {S : Type u} [CommRing S] [Algebra R₀ S] [Algebra R S] [IsScalarTower R₀ R S]
    (ψ : Γ₀ →ₐ[R₀] S) (θ : Γ₀ ⊗[R₀] R ≃ₐ[R₀] S)
    (hθ₁ : ∀ a : Γ₀, θ (a ⊗ₜ (1 : R)) = ψ a) (hθ₂ : ∀ r : R, θ ((1 : Γ₀) ⊗ₜ r) = algebraMap R S r)
    {L₀ : Type v} [AddCommGroup L₀] [Module R₀ L₀]
    {L : Type v} [AddCommGroup L] [Module R L] (eL : R ⊗[R₀] L₀ ≃ₗ[R] L)
    {N₀ : Type w} [AddCommGroup N₀] [Module R₀ N₀] [Module Γ₀ N₀] [IsScalarTower R₀ Γ₀ N₀]
    (f₀ : L₀ →ₗ[R₀] N₀) (hf₀ : IsBaseChange Γ₀ f₀)
    {N : Type w} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : L →ₗ[R] N) (hf : IsBaseChange S f) :
    ∃ Φ : R ⊗[R₀] N₀ ≃ₗ[R] N,
      (∀ x₀ : L₀, Φ ((1 : R) ⊗ₜ f₀ x₀) = f (eL ((1 : R) ⊗ₜ x₀))) ∧
      (∀ (r : R) (γ : Γ₀) (n₀ : N₀), Φ (r ⊗ₜ (γ • n₀)) = r • (ψ γ • Φ ((1 : R) ⊗ₜ n₀))) ∧
      (∀ (N' : Type w) [AddCommGroup N'] [Module R N'] (g g' : R ⊗[R₀] N₀ →ₗ[R] N'),
          (∀ (r : R) (γ : Γ₀) (x₀ : L₀), g (r ⊗ₜ (γ • f₀ x₀)) = g' (r ⊗ₜ (γ • f₀ x₀))) → g = g') := by
  classical

  letI mL : Module R₀ L := Module.compHom L (algebraMap R₀ R)
  haveI tL : IsScalarTower R₀ R L := ⟨fun r₀ r x => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  letI mN : Module R₀ N := Module.compHom N (algebraMap R₀ S)
  haveI tNS : IsScalarTower R₀ S N := ⟨fun r₀ s x => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  haveI tNR : IsScalarTower R₀ R N := ⟨fun r₀ r x => by
    rw [Algebra.smul_def, mul_smul, ← algebraMap_smul S (algebraMap R₀ R r₀), ← IsScalarTower.algebraMap_apply]; rfl⟩

  let l : L₀ →ₗ[R₀] L :=
    { toFun := fun x₀ => eL ((1 : R) ⊗ₜ x₀)
      map_add' := fun x y => by rw [TensorProduct.tmul_add, map_add]
      map_smul' := fun r₀ x => by
        rw [RingHom.id_apply, TensorProduct.tmul_smul, ← algebraMap_smul R r₀, LinearEquiv.map_smul]; rfl }
  have hl : ∀ x₀, l x₀ = eL ((1 : R) ⊗ₜ x₀) := fun _ => rfl
  have hL : IsBaseChange R l := IsBaseChange.of_equiv eL (fun x => rfl)

  have hF : IsBaseChange S ((f.restrictScalars R₀).comp l) := IsBaseChange.comp hL hf

  let θ' : R ⊗[R₀] Γ₀ ≃ₐ[R₀] S := (Algebra.TensorProduct.comm R₀ R Γ₀).trans θ
  have hθ' : ∀ (r : R) (γ : Γ₀), θ' (r ⊗ₜ γ) = θ (γ ⊗ₜ r) := fun r γ => by
    show θ ((Algebra.TensorProduct.comm R₀ R Γ₀) (r ⊗ₜ γ)) = _
    rw [Algebra.TensorProduct.comm_tmul]
  let eS : R ⊗[R₀] Γ₀ ≃ₗ[R] S :=
    { θ'.toLinearEquiv with
      map_smul' := fun r z => by
        show θ' (r • z) = r • θ' z
        rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply, map_mul, hθ',
          hθ₂, ← Algebra.smul_def] }
  have heS : ∀ z, eS z = θ' z := fun _ => rfl
  have hS : IsBaseChange R ψ.toLinearMap :=
    IsBaseChange.of_equiv eS (fun γ => by rw [heS, hθ', hθ₁]; rfl)

  let e₀ : N₀ ≃ₗ[R₀] Γ₀ ⊗[R₀] L₀ := hf₀.equiv.symm.restrictScalars R₀
  let Φ : R ⊗[R₀] N₀ ≃ₗ[R] N :=
    (e₀.baseChange R₀ R N₀ (Γ₀ ⊗[R₀] L₀)) ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.assoc R₀ R₀ R R Γ₀ L₀).symm ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.congr hS.equiv (LinearEquiv.refl R₀ L₀)) ≪≫ₗ
      (hF.equiv.restrictScalars R)

  have hΦ : ∀ (r : R) (γ : Γ₀) (x₀ : L₀), Φ (r ⊗ₜ (γ • f₀ x₀)) = r • (ψ γ • f (eL ((1 : R) ⊗ₜ x₀))) := by
    intro r γ x₀
    have h1 : e₀ (γ • f₀ x₀) = γ ⊗ₜ x₀ := by
      show hf₀.equiv.symm (γ • f₀ x₀) = γ ⊗ₜ x₀
      rw [LinearEquiv.map_smul, IsBaseChange.equiv_symm_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    show hF.equiv ((TensorProduct.AlgebraTensorModule.congr hS.equiv (LinearEquiv.refl R₀ L₀))
      ((TensorProduct.AlgebraTensorModule.assoc R₀ R₀ R R Γ₀ L₀).symm
        ((e₀.baseChange R₀ R N₀ (Γ₀ ⊗[R₀] L₀)) (r ⊗ₜ (γ • f₀ x₀))))) = _
    rw [LinearEquiv.baseChange_tmul, h1, TensorProduct.AlgebraTensorModule.assoc_symm_tmul,
      TensorProduct.AlgebraTensorModule.congr_tmul, IsBaseChange.equiv_tmul, LinearEquiv.refl_apply,
      IsBaseChange.equiv_tmul, smul_assoc]
    rfl
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro x₀
    have := hΦ 1 1 x₀
    rwa [one_smul, map_one, one_smul, one_smul] at this
  ·
    have key : ∀ (n₀ : N₀) (γ : Γ₀), Φ ((1 : R) ⊗ₜ (γ • n₀)) = ψ γ • Φ ((1 : R) ⊗ₜ n₀) := by
      intro n₀
      induction n₀ using hf₀.inductionOn with
      | zero => intro γ; rw [smul_zero, TensorProduct.tmul_zero, map_zero, smul_zero]
      | tmul x₀ =>
        intro γ
        have h1 := hΦ 1 γ x₀
        have h2 := hΦ 1 1 x₀
        rw [one_smul] at h1
        rw [one_smul, map_one, one_smul, one_smul] at h2
        rw [h1, h2]
      | smul s n hn => intro γ; rw [smul_smul, hn, hn, map_mul, mul_smul]
      | add n₁ n₂ h₁ h₂ => intro γ; rw [smul_add, TensorProduct.tmul_add, map_add, h₁, h₂, TensorProduct.tmul_add, map_add, smul_add]
    intro r γ n₀
    have : r ⊗ₜ[R₀] (γ • n₀) = r • ((1 : R) ⊗ₜ[R₀] (γ • n₀)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, LinearEquiv.map_smul, key]
  ·
    intro N' _ _ g g' hgg'
    have key : ∀ (n₀ : N₀) (r : R) (γ : Γ₀), g (r ⊗ₜ (γ • n₀)) = g' (r ⊗ₜ (γ • n₀)) := by
      intro n₀
      induction n₀ using hf₀.inductionOn with
      | zero => intro r γ; rw [smul_zero, TensorProduct.tmul_zero, map_zero, map_zero]
      | tmul x₀ => intro r γ; exact hgg' r γ x₀
      | smul s n hn => intro r γ; rw [smul_smul]; exact hn r (γ * s)
      | add n₁ n₂ h₁ h₂ => intro r γ; rw [smul_add, TensorProduct.tmul_add, map_add, map_add, h₁, h₂]
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul r n₀ => have := key n₀ r 1; rwa [one_smul] at this
    | add a b ha hb => rw [map_add, map_add, ha, hb]

end S_IsBaseChange_exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange
end P2MW
export P2MW.S_IsBaseChange_exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange (solution)
