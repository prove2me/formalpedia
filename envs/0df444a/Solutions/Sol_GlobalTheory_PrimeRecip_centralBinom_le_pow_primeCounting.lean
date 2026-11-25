-- Prove2me | solution 1 for GlobalTheory.PrimeRecip.centralBinom_le_pow_primeCounting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:59:47.494803+00:00
-- url     : https://prove2.me/submissions/cb4b5560-a13a-4256-9d44-805f80b4a2f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvFiveLogLeSumInvPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
open GlobalTheory GlobalTheory.PrimeRecip
namespace GlobalTheory.PrimeRecip
theorem _root_.solution (n : ℕ) (n_large : 2 < n) :
    n.centralBinom ≤ (2 * n) ^ Nat.primeCounting (Nat.sqrt (2 * n)) * 4 ^ (2 * n / 3) *
      (2 * n) ^ ((Finset.range (2 * n + 1)).filter (fun p => p.Prime ∧ n < p)).card := by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_large
  have n2_pos : 1 ≤ 2 * n := mul_pos (zero_lt_two' ℕ) n_pos
  let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
  let T := (Finset.range (2 * n + 1)).filter (fun p => p.Prime ∧ n < p)
  let f : ℕ → ℕ := fun x => x ^ n.centralBinom.factorization x
  have hf : ∀ p, f p ≤ 2 * n := fun p => Nat.pow_factorization_choose_le (mul_pos two_pos n_pos)
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hx hy
    have h1 := Finset.mem_range.1 (Finset.mem_filter.1 hx).1
    have h2 := (Finset.mem_filter.1 hy).2.2
    omega
  have key : n.centralBinom = (∏ x ∈ S, f x) * ∏ x ∈ T, f x := by
    rw [← Finset.prod_union hdisj]
    refine (Eq.trans ?_ n.prod_pow_factorization_centralBinom).symm
    apply Finset.prod_subset
    · intro x hx
      rcases Finset.mem_union.1 hx with h | h
      · have h1 := Finset.mem_range.1 (Finset.mem_filter.1 h).1
        rw [Finset.mem_range]; omega
      · exact (Finset.mem_filter.1 h).1
    intro x hx h2x
    by_cases hp : x.Prime
    · have h1 : ¬ x < 2 * n / 3 + 1 := fun h => h2x (Finset.mem_union.2 (Or.inl
        (Finset.mem_filter.2 ⟨Finset.mem_range.2 h, hp⟩)))
      have h2 : ¬ n < x := fun h => h2x (Finset.mem_union.2 (Or.inr
        (Finset.mem_filter.2 ⟨hx, hp, h⟩)))
      have h3 : 2 * n < 3 * x := by omega
      simp only [f]
      rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul n_large (not_lt.1 h2) h3,
        Nat.pow_zero]
    · simp only [f]
      rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom hp, Nat.pow_zero]
  rw [key]
  apply mul_le_mul'
  · rw [← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt (2 * n))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod' fun p _ => hf p).trans ?_
      rw [Finset.prod_const]
      refine pow_right_mono₀ n2_pos ?_
      rw [← Nat.primesLE_card_eq_primeCounting]
      refine Finset.card_le_card fun x hx => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact Nat.mem_primesLE.2 ⟨h2, (Finset.mem_filter.1 h1).2⟩
    · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
      refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
        refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp <| not_le.1 h2)
      refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
      exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le
  · refine (Finset.prod_le_prod' fun p _ => hf p).trans ?_
    rw [Finset.prod_const]
end GlobalTheory.PrimeRecip
