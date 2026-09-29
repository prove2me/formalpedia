-- Prove2me | solution 1 for Module.Projective.exists_ideal_forall_tmul_eq_zero_iff_map_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/1982bd4f-495e-563a-acfe-1ec2260b87e9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Projective_exists_ideal_forall_tmul_eq_zero_iff_map_eq_bot

set_option autoImplicit false

universe u v

open TensorProduct

theorem solution
    (B : Type u) [CommRing B] (M : Type v) [AddCommGroup M] [Module B M]
    [Module.Finite B M] [Module.Projective B M] (x : M) :
    ∃ J : Ideal B, ∀ (A : Type u) [CommRing A] (φ : B →+* A),
      (letI : Algebra B A := φ.toAlgebra; ((1 : A) ⊗ₜ[B] x : A ⊗[B] M) = 0) ↔ Ideal.map φ J = ⊥ := by
  classical

  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := B) (M := M)
  let p : (Fin n → B) →ₗ[B] M := Fintype.linearCombination B s
  have hp : Function.Surjective p := by
    intro m
    have hm : m ∈ Submodule.span B (Set.range s) := by rw [hs]; exact Submodule.mem_top
    rw [← Fintype.range_linearCombination B s] at hm
    exact hm

  obtain ⟨g, hg⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[B] M) hp
  refine ⟨Ideal.span (Set.range fun i : Fin n => g x i), ?_⟩
  intro A _ φ
  letI : Algebra B A := φ.toAlgebra
  have hφ : ∀ b : B, algebraMap B A b = φ b := fun b => rfl

  have hJ : Ideal.map φ (Ideal.span (Set.range fun i : Fin n => g x i)) = ⊥ ↔ ∀ i, φ (g x i) = 0 := by
    rw [Ideal.map_span, Ideal.span_eq_bot]
    constructor
    · intro h i
      exact h _ ⟨g x i, ⟨i, rfl⟩, rfl⟩
    · rintro h _ ⟨b, ⟨i, rfl⟩, rfl⟩
      exact h i
  rw [hJ]

  have hcoord : ∀ i : Fin n,
      (TensorProduct.rid B A) (LinearMap.lTensor A ((LinearMap.proj i).comp g) ((1 : A) ⊗ₜ[B] x)) = φ (g x i) := by
    intro i
    simp only [LinearMap.lTensor_tmul, LinearMap.comp_apply, LinearMap.proj_apply, TensorProduct.rid_tmul]
    rw [Algebra.smul_def, hφ, mul_one]
  constructor
  ·
    intro h0 i
    have := hcoord i
    rw [h0, map_zero, map_zero] at this
    exact this.symm
  ·
    intro hzero
    have hx : x = p (g x) := by
      have := congrArg (fun f : M →ₗ[B] M => f x) hg
      simpa using this.symm

    have hgx : ((1 : A) ⊗ₜ[B] (g x) : A ⊗[B] (Fin n → B)) = 0 := by
      have hdecomp : g x = ∑ i : Fin n, (g x i) • (Pi.single i (1 : B) : Fin n → B) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hdecomp, TensorProduct.tmul_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, hφ, hzero i, zero_mul, TensorProduct.zero_tmul]
    calc ((1 : A) ⊗ₜ[B] x : A ⊗[B] M) = LinearMap.lTensor A p ((1 : A) ⊗ₜ[B] (g x)) := by
          rw [LinearMap.lTensor_tmul, ← hx]
      _ = 0 := by rw [hgx, map_zero]

end S_Module_Projective_exists_ideal_forall_tmul_eq_zero_iff_map_eq_bot
end P2MW
export P2MW.S_Module_Projective_exists_ideal_forall_tmul_eq_zero_iff_map_eq_bot (solution)
