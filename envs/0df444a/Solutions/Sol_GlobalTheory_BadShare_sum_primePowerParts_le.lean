-- Prove2me | solution 1 for GlobalTheory.BadShare.sum_primePowerParts_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:29:48.832469+00:00
-- url     : https://prove2.me/submissions/49cf4358-f991-4d40-8229-e9a958ea3ff8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumLeProdOfTwoLeNat
import Theorems.Thm_GlobalTheory_BadShare_sum_le_prod_of_two_le_nat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare
private theorem arith_four (a b c R m : ℕ) (ha : 16 ≤ a) (hb : m ≤ b) (hc : m ≤ c)
    (hbc : 16 * m ≤ b * c) (hR : 1 ≤ R) : 4 * m * (a + b + c + R) ≤ a * b * c * R := by
  have h1 : 16 * m * a ≤ b * c * a := Nat.mul_le_mul_right _ hbc
  have h2 : 16 * m * b ≤ a * c * b := Nat.mul_le_mul_right _ (Nat.mul_le_mul ha hc)
  have h3 : 16 * m * c ≤ a * b * c := Nat.mul_le_mul_right _ (Nat.mul_le_mul ha hb)
  have h4 : 16 * m * R ≤ a * b * c * R := by
    apply Nat.mul_le_mul_right
    calc 16 * m ≤ b * c := hbc
      _ ≤ a * (b * c) := Nat.le_mul_of_pos_left _ (by omega)
      _ = a * b * c := by ring
  have h5 : a * b * c ≤ a * b * c * R := Nat.le_mul_of_pos_right _ hR
  nlinarith
end GlobalTheory.BadShare
end

set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution :
    ∀ n q d : ℕ, 0 < n → q.Prime → d.Prime → q ≠ 2 → d ≠ 2 → q ≠ d → 16 ≤ max q d →
      16 * q * d ∣ n → (∑ l ∈ n.primeFactors, ((l ^ padicValNat l n : ℕ) : ℝ)) ≤
        (n : ℝ) / (4 * ((min q d : ℕ) : ℝ)) := by
  intro n q d hn hq hd hq2 hd2 hqd hmax hdvd
  set f : ℕ → ℕ := fun l => l ^ padicValNat l n with hf
  have hpow : ∀ p k : ℕ, p.Prime → p ^ k ∣ n → p ^ k ≤ f p := by
    intro p k hp hk
    haveI := Fact.mk hp
    exact Nat.pow_le_pow_right hp.pos ((padicValNat_dvd_iff_le hn.ne').1 hk)
  have hge : ∀ p ∈ n.primeFactors, p ≤ f p := by
    intro p hp
    have := hpow p 1 (Nat.prime_of_mem_primeFactors hp)
      (by simpa using Nat.dvd_of_mem_primeFactors hp)
    simpa using this
  have h16 : 2 ^ 4 ∣ n := Dvd.dvd.trans ⟨q * d, by ring⟩ hdvd
  have hqn : q ∣ n := Dvd.dvd.trans ⟨16 * d, by ring⟩ hdvd
  have hdn : d ∣ n := Dvd.dvd.trans ⟨16 * q, by ring⟩ hdvd
  have m2 : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.2 ⟨Nat.prime_two, Dvd.dvd.trans ⟨8, by norm_num⟩ h16, hn.ne'⟩
  have mq : q ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hq, hqn, hn.ne'⟩
  have md : d ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hd, hdn, hn.ne'⟩
  have ha : 16 ≤ f 2 := by simpa using hpow 2 4 Nat.prime_two h16
  have hb := hge q mq
  have hc := hge d md
  have hsub : ({2, q, d} : Finset ℕ) ⊆ n.primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hn2 : (2 : ℕ) ∉ ({q, d} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hprod : ∏ l ∈ n.primeFactors, f l = n := by
    conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn.ne']
    rw [Finsupp.prod, Nat.support_factorization]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]
  set s := n.primeFactors \ {2, q, d} with hs
  have hs2 : ∀ i ∈ s, 2 ≤ f i := fun i hi =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.1 hi).1).two_le.trans
      (hge i (Finset.mem_sdiff.1 hi).1)
  have hSP := sum_le_prod_of_two_le_nat s f hs2
  have hR : 1 ≤ ∏ i ∈ s, f i :=
    Finset.prod_pos (f := f) fun i hi => lt_of_lt_of_le (by norm_num) (hs2 i hi)
  have e1 : n = f 2 * f q * f d * ∏ i ∈ s, f i := by
    rw [← hprod, ← Finset.prod_sdiff hsub, Finset.prod_insert hn2, Finset.prod_pair hqd]
    ring
  have e2 : ∑ l ∈ n.primeFactors, f l = f 2 + f q + f d + ∑ i ∈ s, f i := by
    rw [← Finset.sum_sdiff hsub, Finset.sum_insert hn2, Finset.sum_pair hqd]
    ring
  have hbc : 16 * min q d ≤ f q * f d := by
    calc 16 * min q d ≤ max q d * min q d := Nat.mul_le_mul_right _ hmax
      _ = q * d := max_mul_min q d
      _ ≤ f q * f d := Nat.mul_le_mul hb hc
  have key := arith_four (f 2) (f q) (f d) (∏ i ∈ s, f i) (min q d) ha
    ((min_le_left _ _).trans hb) ((min_le_right _ _).trans hc) hbc hR
  rw [← e1] at key
  have key2 : (∑ l ∈ n.primeFactors, f l) * (4 * min q d) ≤ n := by
    rw [e2, mul_comm]
    exact (Nat.mul_le_mul_left _ (by omega)).trans key
  have hm : 0 < min q d := lt_min hq.pos hd.pos
  rw [le_div_iff₀ (by positivity), ← Nat.cast_sum]
  exact_mod_cast key2
end GlobalTheory.BadShare
