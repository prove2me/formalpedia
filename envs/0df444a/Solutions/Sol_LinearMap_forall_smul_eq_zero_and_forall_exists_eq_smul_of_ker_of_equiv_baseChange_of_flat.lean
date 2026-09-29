-- Prove2me | solution 1 for LinearMap.forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/37b2cd30-0cc2-593b-bf64-6317ce283f59

import Mathlib
import Theorems.Thm_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat

set_option autoImplicit false

open scoped TensorProduct

universe u v w w'

theorem solution
    {R₀ : Type u} [CommRing R₀] {R : Type v} [CommRing R] [Algebra R₀ R] [Module.Flat R₀ R]
    {L₀ : Type w} [AddCommGroup L₀] [Module R₀ L₀] {C₀ : Type w} [AddCommGroup C₀] [Module R₀ C₀]
    {D₀ : Type w} [AddCommGroup D₀] [Module R₀ D₀]
    (u₀ : L₀ →ₗ[R₀] C₀) (d₀ : C₀ →ₗ[R₀] D₀) (hdu₀ : ∀ x : L₀, d₀ (u₀ x) = 0) (J : Ideal R₀)
    (hk : ∀ x : L₀, u₀ x = 0 → ∀ a ∈ J, a • x = 0)
    (hc : ∀ y : C₀, d₀ y = 0 → ∀ a ∈ J, ∃ x : L₀, u₀ x = a • y)
    {L : Type w'} [AddCommGroup L] [Module R L] {C : Type w'} [AddCommGroup C] [Module R C]
    {D : Type w'} [AddCommGroup D] [Module R D]
    (u : L →ₗ[R] C) (d : C →ₗ[R] D)
    (eL : R ⊗[R₀] L₀ ≃ₗ[R] L) (eC : R ⊗[R₀] C₀ ≃ₗ[R] C) (eD : R ⊗[R₀] D₀ ≃ₗ[R] D)
    (hu : ∀ x : L₀, u (eL ((1 : R) ⊗ₜ x)) = eC ((1 : R) ⊗ₜ u₀ x))
    (hd : ∀ y : C₀, d (eC ((1 : R) ⊗ₜ y)) = eD ((1 : R) ⊗ₜ d₀ y)) :
    (∀ x : L, u x = 0 → ∀ a ∈ J.map (algebraMap R₀ R), a • x = 0) ∧
    (∀ y : C, d y = 0 → ∀ a ∈ J.map (algebraMap R₀ R), ∃ x : L, u x = a • y) := by
  classical

  set Z₀ := LinearMap.ker d₀ with hZ₀
  let u₀' : L₀ →ₗ[R₀] Z₀ := u₀.codRestrict Z₀ (fun x => by rw [LinearMap.mem_ker]; exact hdu₀ x)
  have hu₀' : ∀ x, (u₀' x : C₀) = u₀ x := fun _ => rfl
  have hsub : Z₀.subtype ∘ₗ u₀' = u₀ := LinearMap.ext fun _ => rfl
  have hk' : ∀ x : L₀, u₀' x = 0 → ∀ a ∈ J, a • x = 0 := fun x hx => hk x (by rw [← hu₀', hx]; rfl)
  have hc' : ∀ (y : Z₀), ∀ a ∈ J, ∃ x : L₀, u₀' x = a • y := fun y a ha => by
    obtain ⟨x, hx⟩ := hc y.1 y.2 a ha
    exact ⟨x, Subtype.ext (by rw [hu₀', hx]; rfl)⟩
  obtain ⟨h1, h2⟩ := LinearMap.forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat (R := R) u₀' J hk' hc'

  have hinj : Function.Injective (Z₀.subtype.baseChange R) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype Z₀)
  have hexact : Function.Exact (Z₀.subtype.baseChange R) (d₀.baseChange R) := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_exact R (LinearMap.exact_subtype_ker_map d₀)
  have hcompu : ∀ x, u₀.baseChange R x = Z₀.subtype.baseChange R (u₀'.baseChange R x) := fun x => by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hsub]

  have hA : ∀ x, u (eL x) = eC (u₀.baseChange R x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      rw [show r ⊗ₜ[R₀] x = r • ((1 : R) ⊗ₜ[R₀] x) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        map_smul, map_smul, hu, map_smul, map_smul, LinearMap.baseChange_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hB : ∀ y, d (eC y) = eD (d₀.baseChange R y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r y =>
      rw [show r ⊗ₜ[R₀] y = r • ((1 : R) ⊗ₜ[R₀] y) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        map_smul, map_smul, hd, map_smul, map_smul, LinearMap.baseChange_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  refine ⟨fun x hx a ha => ?_, fun y hy a ha => ?_⟩
  · obtain ⟨x', rfl⟩ := eL.surjective x
    have h0 : u₀'.baseChange R x' = 0 := by
      apply hinj
      rw [map_zero, ← hcompu]
      apply eC.injective
      rw [map_zero, ← hA, hx]
    rw [← map_smul, h1 x' h0 a ha, map_zero]
  · obtain ⟨y', rfl⟩ := eC.surjective y
    have hd0 : d₀.baseChange R y' = 0 := by
      apply eD.injective
      rw [map_zero, ← hB, hy]
    obtain ⟨z, hz⟩ := (hexact y').mp hd0
    obtain ⟨x', hx'⟩ := h2 z a ha
    refine ⟨eL x', ?_⟩
    rw [hA, hcompu, hx', map_smul, hz, map_smul]

end S_LinearMap_forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat
end P2MW
export P2MW.S_LinearMap_forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat (solution)
