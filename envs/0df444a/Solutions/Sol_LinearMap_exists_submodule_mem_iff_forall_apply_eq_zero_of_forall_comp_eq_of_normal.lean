-- Prove2me | solution 1 for LinearMap.exists_submodule_mem_iff_forall_apply_eq_zero_of_forall_comp_eq_of_normal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d91c4bb1-f6ab-569c-a492-f83af581d135

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_exists_submodule_mem_iff_forall_apply_eq_zero_of_forall_comp_eq_of_normal

set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R] [IsDomain R]
    {Γ : Type*} [Group Γ] {T : Type*} [AddCommGroup T] [Module R T]
    (ρ : Γ →* Module.End R T) (I : Subgroup Γ) (hI : I.Normal)
    (f : T →ₗ[R] R) (hf : ∀ τ ∈ I, f ∘ₗ ρ τ = f) :
    ∃ M : Submodule R T,
      (∀ x : T, x ∈ M ↔ ∀ γ : Γ, f (ρ γ x) = 0) ∧
      (∀ (γ : Γ) (x : T), x ∈ M → ρ γ x ∈ M) ∧
      (∀ τ ∈ I, ∀ x : T, ρ τ x - x ∈ M) ∧
      (∀ (r : R) (x : T), r ≠ 0 → r • x ∈ M → x ∈ M) ∧
      (∀ x ∈ M, f x = 0) := by

  let M : Submodule R T :=
    { carrier := {x | ∀ γ : Γ, f (ρ γ x) = 0}
      add_mem' := by
        intro x y hx hy γ
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_add, map_add, hx γ, hy γ, add_zero]
      zero_mem' := by
        intro γ
        rw [map_zero, map_zero]
      smul_mem' := by
        intro r x hx γ
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [map_smul, map_smul, hx γ, smul_zero] }
  have hM : ∀ x : T, x ∈ M ↔ ∀ γ : Γ, f (ρ γ x) = 0 := fun x => Iff.rfl
  refine ⟨M, hM, ?_, ?_, ?_, ?_⟩
  ·
    intro γ x hx
    rw [hM] at hx ⊢
    intro γ'
    rw [← Module.End.mul_apply, ← map_mul]
    exact hx (γ' * γ)
  ·
    intro τ hτ x
    rw [hM]
    intro γ
    have hconj : γ * τ * γ⁻¹ ∈ I := hI.conj_mem τ hτ γ
    have h1 : ρ γ (ρ τ x) = ρ (γ * τ * γ⁻¹) (ρ γ x) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    have h2 : f (ρ (γ * τ * γ⁻¹) (ρ γ x)) = f (ρ γ x) := by
      have := hf _ hconj
      exact LinearMap.congr_fun this (ρ γ x)
    rw [map_sub, map_sub, h1, h2, sub_self]
  ·
    intro r x hr hx
    rw [hM] at hx ⊢
    intro γ
    have h := hx γ
    rw [map_smul, map_smul, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hr
  ·
    intro x hx
    rw [hM] at hx
    simpa using hx 1

end S_LinearMap_exists_submodule_mem_iff_forall_apply_eq_zero_of_forall_comp_eq_of_normal
end P2MW
export P2MW.S_LinearMap_exists_submodule_mem_iff_forall_apply_eq_zero_of_forall_comp_eq_of_normal (solution)
