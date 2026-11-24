-- Prove2me | solution 1 for GlobalTheory.exists_isotropic_dual_of_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:42:40.248931+00:00
-- url     : https://prove2.me/submissions/c331f26a-448b-4e08-b704-6601556f4a04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsIsotropicDualOfSkewMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℚ V] {g : ℕ}
    (B : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (ε ψ : Fin g → V) (hB : ∀ x y, B x y = -B y x)
    (hε : ∀ i j, B (ε i) (ε j) = 0)
    (hψ : ∀ i j, B (ψ j) (ε i) = if i = j then 1 else 0) :
    ∃ φ : Fin g → V, (∀ i j, B (φ i) (φ j) = 0) ∧
      (∀ i j, B (φ j) (ε i) = if i = j then 1 else 0) ∧
      ∀ j, φ j - ψ j ∈ Submodule.span ℚ (Set.range ε) := by
  classical
  have h1 : ∀ k l, B (ψ l) (ε k) = if k = l then 1 else 0 := fun k l => hψ k l
  have h2 : ∀ k l, B (ε k) (ψ l) = -(if k = l then 1 else 0) := fun k l => by
    rw [hB, h1]
  refine ⟨fun j => ψ j + ∑ k, (B (ψ j) (ψ k) / 2) • ε k, ?_, ?_, ?_⟩
  · intro i j
    simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hε, h1, h2, mul_zero,
      Finset.sum_const_zero, add_zero, mul_ite, mul_one, mul_neg, Finset.sum_neg_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linarith [hB (ψ i) (ψ j)]
  · intro i j
    simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hε, h1, mul_zero,
      Finset.sum_const_zero, add_zero]
  · intro j
    simp only [add_sub_cancel_left]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
end GlobalTheory
