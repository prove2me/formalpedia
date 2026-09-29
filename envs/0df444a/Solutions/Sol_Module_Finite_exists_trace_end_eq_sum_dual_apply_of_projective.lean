-- Prove2me | solution 1 for Module.Finite.exists_trace_end_eq_sum_dual_apply_of_projective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/34e938b0-4ec2-5835-b122-9a1a3e03c79f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Finite_exists_trace_end_eq_sum_dual_apply_of_projective

set_option autoImplicit false

universe u v

open scoped BigOperators

namespace TraceDual

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

theorem sum_dual_apply_eq
    {n : ℕ} (x : Fin n → M) (φ : Fin n → (M →ₗ[A] A)) (hxφ : ∀ m : M, ∑ i, φ i m • x i = m)
    {n' : ℕ} (y : Fin n' → M) (ψ : Fin n' → (M →ₗ[A] A)) (hyψ : ∀ m : M, ∑ j, ψ j m • y j = m)
    (f : M →ₗ[A] M) :
    ∑ j, ψ j (f (y j)) = ∑ i, φ i (f (x i)) := by
  calc ∑ j, ψ j (f (y j)) = ∑ j, ψ j (∑ i, φ i (f (y j)) • x i) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hxφ]
    _ = ∑ j, ∑ i, φ i (f (y j)) * ψ j (x i) := by
        simp only [map_sum, map_smul, smul_eq_mul]
    _ = ∑ i, ∑ j, ψ j (x i) * φ i (f (y j)) := by
        rw [Finset.sum_comm]
        simp only [mul_comm]
    _ = ∑ i, φ i (f (∑ j, ψ j (x i) • y j)) := by
        simp only [map_sum, map_smul, smul_eq_mul]
    _ = ∑ i, φ i (f (x i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hyψ]

variable [Module.Finite A M] [Module.Projective A M]

theorem exists_dual_family :
    ∃ (n : ℕ) (x : Fin n → M) (φ : Fin n → (M →ₗ[A] A)), ∀ m : M, ∑ i, φ i m • x i = m := by
  obtain ⟨n, π, s, -, -, hπs⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  refine ⟨n, fun i => π (Pi.single i 1), fun i => (LinearMap.proj i).comp s, fun m => ?_⟩
  have hsum : ∑ i, (s m i) • (Pi.single i (1 : A) : Fin n → A) = s m := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply, eq_comm]
  calc ∑ i, ((LinearMap.proj i).comp s) m • π (Pi.single i 1)
        = π (∑ i, (s m i) • (Pi.single i (1 : A) : Fin n → A)) := by
          simp only [map_sum, map_smul, LinearMap.coe_comp, Function.comp_apply,
            LinearMap.coe_proj, Function.eval]
    _ = m := by rw [hsum, ← LinearMap.comp_apply, hπs, LinearMap.id_apply]

end TraceDual

theorem solution
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] :
    ∃ τ : (M →ₗ[A] M) →ₗ[A] A,
      ∀ (n : ℕ) (x : Fin n → M) (φ : Fin n → (M →ₗ[A] A)),
        (∀ m : M, ∑ i, φ i m • x i = m) →
          ∀ f : M →ₗ[A] M, τ f = ∑ i, φ i (f (x i)) := by
  obtain ⟨n₀, y, ψ, hyψ⟩ := TraceDual.exists_dual_family (A := A) (M := M)
  refine ⟨{ toFun := fun f => ∑ j, ψ j (f (y j))
            map_add' := fun f g => by simp [Finset.sum_add_distrib]
            map_smul' := fun a f => by simp [Finset.mul_sum] }, ?_⟩
  intro n x φ hxφ f
  exact TraceDual.sum_dual_apply_eq x φ hxφ y ψ hyψ f

end S_Module_Finite_exists_trace_end_eq_sum_dual_apply_of_projective
end P2MW
export P2MW.S_Module_Finite_exists_trace_end_eq_sum_dual_apply_of_projective (solution)
