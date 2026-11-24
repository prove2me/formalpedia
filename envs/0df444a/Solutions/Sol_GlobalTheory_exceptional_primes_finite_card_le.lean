-- Prove2me | solution 1 for GlobalTheory.exceptional_primes_finite_card_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:38:06.289957+00:00
-- url     : https://prove2.me/submissions/9ecb4576-84dc-4f7c-8d50-17cb3a0c1b0a

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExceptionalPrimesFiniteCardLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (n m : ℕ) (hn : n ≠ 0) (hm : n < m) :
    Set.Finite {ℓ : ℕ | ℓ.Prime ∧ m < ℓ ^ (4 * padicValNat ℓ n)} ∧
      Set.ncard {ℓ : ℕ | ℓ.Prime ∧ m < ℓ ^ (4 * padicValNat ℓ n)} ≤ 3 := by
  classical
  set F : Finset ℕ := n.primeFactors.filter (fun ℓ => m < ℓ ^ (4 * padicValNat ℓ n)) with hF
  have hS : {ℓ : ℕ | ℓ.Prime ∧ m < ℓ ^ (4 * padicValNat ℓ n)} = (F : Set ℕ) := by
    ext ℓ
    simp only [hF, Set.mem_ofPred_eq, coe_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, h⟩
      refine ⟨⟨hp, ?_, hn⟩, h⟩
      by_contra hd
      rw [padicValNat.eq_zero_of_not_dvd hd] at h
      simp at h
      omega
    · rintro ⟨⟨hp, -, -⟩, h⟩
      exact ⟨hp, h⟩
  rw [hS]
  refine ⟨F.finite_toSet, ?_⟩
  rw [Set.ncard_coe_finset]
  by_contra hc
  have hc4 : 4 ≤ F.card := by omega
  have h1 : ∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n ≤ n := by
    have e : ∏ ℓ ∈ n.primeFactors, ℓ ^ padicValNat ℓ n = n := by
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
      rw [Finsupp.prod, Nat.support_factorization]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp)]
    have hd : ∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n ∣ n := by
      conv_rhs => rw [← e]
      exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  have h2 : m ^ F.card ≤ ∏ ℓ ∈ F, ℓ ^ (4 * padicValNat ℓ n) :=
    Finset.pow_card_le_prod F _ m fun ℓ hℓ => ((Finset.mem_filter.1 hℓ).2).le
  have h3 : ∏ ℓ ∈ F, ℓ ^ (4 * padicValNat ℓ n) = (∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n) ^ 4 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, mul_comm]
  have h4 : m ^ 4 ≤ m ^ F.card := Nat.pow_le_pow_right (by omega) hc4
  have h5 : (∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n) ^ 4 ≤ n ^ 4 := Nat.pow_le_pow_left h1 4
  have h6 : n ^ 4 < m ^ 4 := Nat.pow_lt_pow_left hm (by norm_num)
  omega
end GlobalTheory
