-- Prove2me | solution 1 for GlobalTheory.BadShare.inv_log_le_sum_inv_primes_between
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:05:07.198657+00:00
-- url     : https://prove2.me/submissions/a3fea9b1-6f1c-447a-92e3-d94784144448

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralBinomLePowCardPrimesBetween
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
open Polynomial Classical in
private lemma centralBinom_le_pow_mul_four_pow_mul_prod_large_primes (m : ℕ) (hm : 2 < m) :
    m.centralBinom ≤ (2 * m) ^ (Nat.sqrt (2 * m) + 1) * 4 ^ (2 * m / 3) *
      ∏ p ∈ (Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p), p := by
  set s := Nat.sqrt (2 * m) with hs
  have hone : ∀ (P : Prop) [Decidable P] (p : ℕ), (P → 1 ≤ p) → 1 ≤ (if P then p else 1) := by
    intro P _ p h
    split_ifs with hP
    exacts [h hP, le_rfl]
  have key : ∀ p ∈ Finset.range (2 * m + 1), p ^ m.centralBinom.factorization p ≤
      (if p ≤ s then 2 * m else 1) * (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1) *
        (if p.Prime ∧ m < p then p else 1) := by
    intro p _
    have hB : 1 ≤ (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1) :=
      hone _ _ fun h => h.1.one_lt.le
    have hC : 1 ≤ (if p.Prime ∧ m < p then p else 1) := hone _ _ fun h => h.1.one_lt.le
    have hBC : 1 ≤ (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1) *
        (if p.Prime ∧ m < p then p else 1) := le_trans (by norm_num) (Nat.mul_le_mul hB hC)
    by_cases h1 : p ≤ s
    · rw [if_pos h1]
      have h2 : p ^ m.centralBinom.factorization p ≤ 2 * m := by
        rw [Nat.centralBinom_eq_two_mul_choose]
        exact Nat.pow_factorization_choose_le (by omega)
      calc p ^ m.centralBinom.factorization p ≤ 2 * m * 1 * 1 := by simpa using h2
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hB) hC
    · rw [if_neg h1, one_mul]
      have hsq : 2 * m < p ^ 2 :=
        calc 2 * m < (s + 1) ^ 2 := Nat.lt_succ_sqrt' (2 * m)
          _ ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hv : m.centralBinom.factorization p ≤ 1 := by
        rw [Nat.centralBinom_eq_two_mul_choose]
        exact Nat.factorization_choose_le_one hsq
      by_cases hp : p.Prime
      · by_cases h3 : p ≤ 2 * m / 3
        · have h4 : ¬ m < p := by omega
          rw [if_pos ⟨hp, h3⟩, if_neg (fun h => h4 h.2), mul_one]
          calc p ^ m.centralBinom.factorization p ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hv
            _ = p := pow_one p
        · by_cases h5 : m < p
          · rw [if_neg (fun h => h3 h.2), if_pos ⟨hp, h5⟩, one_mul]
            calc p ^ m.centralBinom.factorization p ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hv
              _ = p := pow_one p
          · have h0 : m.centralBinom.factorization p = 0 :=
              Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hm (by omega) (by omega)
            rw [h0, pow_zero]
            exact hBC
      · rw [Nat.factorization_eq_zero_of_not_prime _ hp, pow_zero]
        exact hBC
  calc m.centralBinom
      = ∏ p ∈ Finset.range (2 * m + 1), p ^ m.centralBinom.factorization p :=
        (Nat.prod_pow_factorization_centralBinom m).symm
    _ ≤ ∏ p ∈ Finset.range (2 * m + 1), ((if p ≤ s then 2 * m else 1) *
          (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1) * (if p.Prime ∧ m < p then p else 1)) :=
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _) key
    _ = (∏ p ∈ Finset.range (2 * m + 1), (if p ≤ s then 2 * m else 1)) *
          (∏ p ∈ Finset.range (2 * m + 1), (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1)) *
          (∏ p ∈ Finset.range (2 * m + 1), (if p.Prime ∧ m < p then p else 1)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ ≤ _ := by
        gcongr ?_ * ?_ * ?_
        · rw [← Finset.prod_filter, Finset.prod_const]
          apply Nat.pow_le_pow_right (by omega)
          calc ((Finset.range (2 * m + 1)).filter (fun p => p ≤ s)).card
              ≤ (Finset.range (s + 1)).card := by
                apply Finset.card_le_card
                intro x hx
                simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
                omega
            _ = s + 1 := Finset.card_range _
        · rw [← Finset.prod_filter]
          calc ∏ p ∈ (Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ p ≤ 2 * m / 3), p
              = primorial (2 * m / 3) := by
                unfold primorial
                congr 1
                ext p
                simp only [Finset.mem_filter, Finset.mem_range]
                constructor
                · rintro ⟨_, h2, h3⟩
                  exact ⟨by omega, h2⟩
                · rintro ⟨h1, h2⟩
                  exact ⟨by omega, h2, by omega⟩
            _ ≤ 4 ^ (2 * m / 3) := primorial_le_4_pow _
        · rw [← Finset.prod_filter]
end GlobalTheory.BadShare
end

set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
open Polynomial Classical
namespace GlobalTheory.BadShare
namespace _root_.GlobalTheory.BadShare
theorem _root_.solution :
    ∀ N : ℕ, 100000 ≤ N → 1 / (10 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p := by
  intro N hN
  set S := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) with hS
  set m := N / 2 with hm
  set s := Nat.sqrt (2 * m) with hs
  set k := S.card with hk
  set q := 2 * m / 3 with hq
  have hm3 : 2 < m := by omega
  have hT : ∏ p ∈ (Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p), p ≤
      N ^ 3 * N ^ k := by
    rw [← Finset.prod_filter_mul_prod_filter_not
      ((Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p)) (· ∈ S), mul_comm]
    apply Nat.mul_le_mul
    · have hsub : ((Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p)).filter
          (fun x => x ∉ S) ⊆ Finset.Icc (N - 2) N := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx
        obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hx
        have h5 : ¬ (x + 3 ≤ N) := fun h5 => h4 (by
          rw [hS]
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, h2, by omega, h5⟩)
        rw [Finset.mem_Icc]
        omega
      calc _ ≤ N ^ (((Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p)).filter
            (fun x => x ∉ S)).card :=
            Finset.prod_le_pow_card _ _ _ (fun x hx => (Finset.mem_Icc.mp (hsub hx)).2)
        _ ≤ N ^ 3 := by
            apply Nat.pow_le_pow_right (by omega)
            calc _ ≤ (Finset.Icc (N - 2) N).card := Finset.card_le_card hsub
              _ = 3 := by rw [Nat.card_Icc]; omega
    · calc _ ≤ ∏ x ∈ S, x := by
            apply Finset.prod_le_prod_of_subset_of_one_le'
            · intro x hx
              exact (Finset.mem_filter.mp hx).2
            · intro x hx _
              rw [hS] at hx
              exact (Finset.mem_filter.mp hx).2.1.one_lt.le
        _ ≤ N ^ k := Finset.prod_le_pow_card _ _ _ (fun x hx => by
            rw [hS] at hx
            have := (Finset.mem_filter.mp hx).1
            rw [Finset.mem_range] at this
            omega)
  have hnat : 4 ^ m < N ^ (s + 5 + k) * 4 ^ q := by
    calc 4 ^ m < m * m.centralBinom := Nat.four_pow_lt_mul_centralBinom m (by omega)
      _ ≤ N * ((2 * m) ^ (s + 1) * 4 ^ q * (N ^ 3 * N ^ k)) :=
          Nat.mul_le_mul (by omega)
            (le_trans (centralBinom_le_pow_mul_four_pow_mul_prod_large_primes m hm3)
              (Nat.mul_le_mul_left _ hT))
      _ ≤ N * (N ^ (s + 1) * 4 ^ q * (N ^ 3 * N ^ k)) := by
          gcongr
          omega
      _ = N ^ (s + 5 + k) * 4 ^ q := by ring
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hreal : (m : ℝ) * Real.log 4 < (s + 5 + k) * Real.log N + q * Real.log 4 := by
    have h' : (4 : ℝ) ^ m < (N : ℝ) ^ (s + 5 + k) * (4 : ℝ) ^ q := by exact_mod_cast hnat
    have h2 := Real.log_lt_log (by positivity) h'
    rw [Real.log_mul (pow_pos hN0 _).ne' (by positivity), Real.log_pow, Real.log_pow,
      Real.log_pow] at h2
    push_cast at h2
    linarith
  have hq3 : (3 : ℝ) * q ≤ 2 * m := by exact_mod_cast (by omega : 3 * q ≤ 2 * m)
  have hmN : (N : ℝ) ≤ 2 * m + 1 := by exact_mod_cast (by omega : N ≤ 2 * m + 1)
  have hs2 : (s : ℝ) ^ 2 ≤ N := by
    have : s ^ 2 ≤ N := le_trans (Nat.sqrt_le' (2 * m)) (by omega)
    exact_mod_cast this
  set t := Real.sqrt N with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = N := Real.sq_sqrt hN0.le
  have hNbig : (100000 : ℝ) ≤ N := by exact_mod_cast hN
  have hst : (s : ℝ) ≤ t := by nlinarith [Nat.cast_nonneg (α := ℝ) s]
  have htlow : (316 : ℝ) ≤ t := by nlinarith
  have hL : Real.log N ≤ 7.72 + t / 50 := by
    have h1 := Real.log_le_sub_one_of_pos (x := t / 100) (by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h1
    have h2 : Real.log t = Real.log N / 2 := by rw [ht, Real.log_sqrt hN0.le]
    have h3 : Real.log 100 < 4.86 := by
      have : Real.log 100 < Real.log (2 ^ 7) := Real.log_lt_log (by norm_num) (by norm_num)
      rw [Real.log_pow] at this
      push_cast at this
      linarith [Real.log_two_lt_d9]
    linarith
  have hL4 : 1.386 < Real.log 4 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_gt_d9]
  have hLpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hsum : (k : ℝ) * (1 / N) ≤ ∑ p ∈ S, (1 : ℝ) / p := by
    rw [hk, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    rw [hS] at hp
    obtain ⟨h1, h2, _⟩ := Finset.mem_filter.mp hp
    rw [Finset.mem_range] at h1
    apply one_div_le_one_div_of_le (by exact_mod_cast h2.pos)
    exact_mod_cast (by omega : p ≤ N)
  have hA : ((m : ℝ) - q) * 1.386 ≤ (m : ℝ) * Real.log 4 - q * Real.log 4 := by
    nlinarith
  have hB : ((s : ℝ) + 5) * Real.log N ≤ (t + 5) * (7.72 + t / 50) :=
    mul_le_mul (by linarith) hL hLpos.le (by positivity)
  have hkey : (N : ℝ) ≤ k * (10 * Real.log N) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr htlow) ht0]
  calc 1 / (10 * Real.log N) ≤ k * (1 / N) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) hN0]
        linarith
    _ ≤ _ := hsum
end _root_.GlobalTheory.BadShare
end GlobalTheory.BadShare
