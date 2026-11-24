-- Prove2me | solution 1 for GlobalTheory.exists_diagonal_operator_killing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:39:44.292023+00:00
-- url     : https://prove2.me/submissions/46a85336-3e5b-4aba-b3b9-8baa0af33947

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SimultaneousEigenbasisIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R : Subring ℂ) {g : ℕ} {V : Type} [AddCommGroup V]
    [Module R V] (ψ : V →ₗ[R] (Fin g → ℂ)) {J : Type} (T : J → V →ₗ[R] V) (lam : J → Fin g → ℂ)
    (hT : ∀ a v j, ψ (T a v) j = lam a j * ψ v j)
    (hsep : ∀ j k, j ≠ k → ∃ a, lam a j ≠ lam a k)
    (hK : ∀ a j, ∃ x ∈ R, ∃ y ∈ R, y ≠ 0 ∧ lam a j * y = x) (i : Fin g) (s : Finset (Fin g))
    (hi : i ∉ s) :
    ∃ (P : V →ₗ[R] V) (C : Fin g → ℂ), C i ≠ 0 ∧ (∀ k ∈ s, C k = 0) ∧
      ∀ v k, ψ (P v) k = C k * ψ v k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨LinearMap.id, fun _ => 1, one_ne_zero, by simp, by simp⟩
  | insert j s hj ih =>
    rw [Finset.mem_insert, not_or] at hi
    obtain ⟨P, C, hC, hCs, hP⟩ := ih hi.2
    obtain ⟨a, ha⟩ := hsep i j hi.1
    obtain ⟨x, hx, y, hy, hy0, hxy⟩ := hK a j
    refine ⟨((⟨y, hy⟩ : R) • T a - (⟨x, hx⟩ : R) • LinearMap.id) ∘ₗ P,
      fun k => y * (lam a k - lam a j) * C k, ?_, ?_, ?_⟩
    · exact mul_ne_zero (mul_ne_zero hy0 (sub_ne_zero.mpr ha)) hC
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · simp
      · simp [hCs k hk]
    · intro v k
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_sub,
        map_smul, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply, hT, hP, Subring.smul_def,
        smul_eq_mul]
      rw [← hxy]; ring
end GlobalTheory
