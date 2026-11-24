-- Prove2me | solution 1 for GlobalTheory.FiniteCover.exists_common_multiple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:08:02.688479+00:00
-- url     : https://prove2.me/submissions/68fc1b60-e582-45e2-a3a5-b38f77c77c3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCommonMultiple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.FiniteCover
namespace GlobalTheory.FiniteCover
theorem _root_.solution {F I : Type*} [Field F] [Fintype I] (A : I → Subring F) (ρ c : I → F)
    (hρ : ∀ i, ρ i ≠ 0) (hc : ∀ i, c i ≠ 0) (hr : ∀ i k, ρ i / ρ k ∈ A k)
    (hext : ∀ i k, ∃ m : ℕ, c i * (ρ i / ρ k) ^ m ∈ A k) :
    ∃ (a : ℕ) (u : F), u ≠ 0 ∧ ∀ i, ∃ b ∈ A i, u = ρ i ^ a * c i * b := by
  classical
  choose m hm using hext
  let M : I → ℕ := fun i => ∑ k, m i k
  have hM : ∀ i k, c i * (ρ i / ρ k) ^ M i ∈ A k := fun i k => by
    obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le
      (Finset.single_le_sum (f := m i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
    change c i * (ρ i / ρ k) ^ (∑ k, m i k) ∈ A k
    rw [hl, pow_add, ← mul_assoc]
    exact mul_mem (hm i k) (pow_mem (hr i k) _)
  refine ⟨∑ i, M i, ∏ i, c i * ρ i ^ M i,
    Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (hc i) (pow_ne_zero _ (hρ i)), fun k => ?_⟩
  refine ⟨∏ i ∈ Finset.univ.erase k, c i * (ρ i / ρ k) ^ M i, prod_mem fun i _ => hM i k, ?_⟩
  have e : ∀ i, c i * ρ i ^ M i = ρ k ^ M i * (c i * (ρ i / ρ k) ^ M i) := fun i => by
    have := hρ k
    rw [div_pow]
    field_simp
  rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ k), div_self (hρ k), one_pow, mul_one, mul_assoc]
end GlobalTheory.FiniteCover
