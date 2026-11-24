-- Prove2me | solution 1 for GlobalTheory.exists_compatible_generators_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:55:29.725345+00:00
-- url     : https://prove2.me/submissions/188a48da-3199-426b-ba26-bbef6bffd671

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompatibleGeneratorsTowerLocalRing
import Theorems.Thm_GlobalTheory_exists_surjective_lift_of_ker_le_maximalIdeal_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped TensorProduct
namespace GlobalTheory
private theorem tower_minimal_presentation (Λ : Type) [CommRing Λ] [IsLocalRing Λ] (A : Type)
    [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] :
    ∃ (d : ℕ) (p : (Fin d → Λ) →ₗ[Λ] A), Function.Surjective p ∧
      ∀ x, p x = 0 → ∀ i, x i ∈ IsLocalRing.maximalIdeal Λ := by
  classical
  let k := IsLocalRing.ResidueField Λ
  let b := Module.finBasis k (k ⊗[Λ] A)
  have hs : Function.Surjective (TensorProduct.mk Λ k A 1) :=
    TensorProduct.mk_surjective Λ A k IsLocalRing.residue_surjective
  choose v hv using fun i => hs (b i)
  have hv' : ∀ i, (1 : k) ⊗ₜ[Λ] v i = b i := hv
  have hspan : Submodule.span Λ (Set.range v) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis v b hv'
  refine ⟨_, Fintype.linearCombination Λ v, ?_, ?_⟩
  · rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]
  · intro x hx i
    have h1 : ∑ j, algebraMap Λ k (x j) • b j = 0 := by
      have h2 := congrArg (TensorProduct.mk Λ k A 1) hx
      rw [Fintype.linearCombination_apply, map_sum, map_zero] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, hv, algebraMap_smul]
    have h3 := Fintype.linearIndependent_iff.1 b.linearIndependent _ h1 i
    exact (IsLocalRing.residue_eq_zero_iff _).1 h3
end GlobalTheory
end

set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] (M : ℕ → Type) [∀ n, AddCommGroup (M n)] [∀ n, Module Λ (M n)] [∀ n, Module.Finite Λ (M n)]
  (t : ∀ n, M (n + 1) →ₗ[Λ] M n), (∀ n, Function.Surjective (t n)) →
  (∀ n, LinearMap.ker (t n) ≤ IsLocalRing.maximalIdeal Λ • (⊤ : Submodule Λ (M (n + 1)))) →
  ∃ (a : ℕ) (p : ∀ n, (Fin a → Λ) →ₗ[Λ] M n), (∀ n, Function.Surjective (p n)) ∧ (∀ n, (t n) ∘ₗ (p (n + 1)) = p n) ∧
    ∀ x, p 0 x = 0 → ∀ i, x i ∈ IsLocalRing.maximalIdeal Λ := by
  intro Λ _ _ M _ _ _ t ht hk
  obtain ⟨a, p0, hp0, hmin⟩ := tower_minimal_presentation Λ (M 0)
  choose q hq hq' using fun (n : ℕ) (p : (Fin a → Λ) →ₗ[Λ] M n) (hp : Function.Surjective p) =>
    exists_surjective_lift_of_ker_le_maximalIdeal_smul (t n) (ht n) (hk n) p hp
  let P : ∀ n, {p : (Fin a → Λ) →ₗ[Λ] M n // Function.Surjective p} := fun n =>
    Nat.rec (motive := fun n => {p : (Fin a → Λ) →ₗ[Λ] M n // Function.Surjective p})
      ⟨p0, hp0⟩ (fun n p => ⟨q n p.1 p.2, hq n p.1 p.2⟩) n
  exact ⟨a, fun n => (P n).1, fun n => (P n).2, fun n => hq' n (P n).1 (P n).2, hmin⟩
end GlobalTheory
