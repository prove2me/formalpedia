-- Prove2me | solution 1 for GlobalTheory.PrimeLogSum.sum_log_div_pred_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:21:44.450802+00:00
-- url     : https://prove2.me/submissions/d7f6e4b3-813a-4c4e-aea7-7413b33d5398

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumPrimeLogDivPredLeLogAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.PrimeLogSum
open Finset
open Finset in
private lemma log_three_lt_one_point_one_one : Real.log 3 < 1.11 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.add_one_le_exp 0.11
  have h3 : Real.exp 1.11 = Real.exp 1 * Real.exp 0.11 := by
    rw [← Real.exp_add]; norm_num
  rw [h3]
  nlinarith
open Finset in
private lemma log_succ_div_le_telescoping_sub (n : ℕ) (hn : 3 ≤ n) :
    Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1))
      ≤ (Real.log n + 4 / 3) / n - (Real.log ((n + 1 : ℕ) : ℝ) + 4 / 3) / ((n + 1 : ℕ) : ℝ) := by
  push_cast
  set x : ℝ := (n : ℝ) with hx
  have hx3 : (3 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have hd : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    rw [Real.log_div (by positivity) hx0.ne'] at h
    have : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    linarith
  have h1 : (x + 1) * (Real.log (x + 1) - Real.log x) ≤ (x + 1) * (1 / x) :=
    mul_le_mul_of_nonneg_left hd (by linarith)
  have h2 : (x + 1) * (1 / x) ≤ 4 / 3 := by
    rw [mul_one_div, div_le_iff₀ hx0]; linarith
  have key : Real.log (x + 1)
      ≤ (x + 1) * (Real.log x + 4 / 3) - x * (Real.log (x + 1) + 4 / 3) := by
    nlinarith
  have hpos : 0 < (x + 1) * x := by positivity
  calc Real.log (x + 1) / ((x + 1) * (x + 1 - 1))
      = Real.log (x + 1) / ((x + 1) * x) := by ring_nf
    _ ≤ ((x + 1) * (Real.log x + 4 / 3) - x * (Real.log (x + 1) + 4 / 3)) / ((x + 1) * x) :=
        div_le_div_of_nonneg_right key hpos.le
    _ = (Real.log x + 4 / 3) / x - (Real.log (x + 1) + 4 / 3) / (x + 1) := by
        field_simp
open Finset in
private lemma sum_log_div_mul_pred_add_le_const (N : ℕ) (hN : 3 ≤ N) :
    ∑ n ∈ Finset.range (N + 1), Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) + (Real.log N + 4 / 3) / N
      ≤ Real.log 2 / 2 + Real.log 3 / 6 + (Real.log 3 + 4 / 3) / 3 := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp [Finset.sum_range_succ]
    norm_num
  | succ n hn ih =>
    rw [Finset.sum_range_succ]
    have := log_succ_div_le_telescoping_sub n hn
    linarith
open Finset in
private lemma div_le_factorization_factorial' (N p : ℕ) (hp : p.Prime) :
    N / p ≤ (N.factorial).factorization p := by
  rw [Nat.factorization_factorial hp (lt_add_one (Nat.log p N))]
  rcases Nat.lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  · have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
      simp [Nat.log_pos hp.one_lt h]
    simpa using single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _) h1
open Finset in
private lemma mul_sum_prime_log_div_le_log_factorial_add (N : ℕ) :
    (N : ℝ) * ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / p
      ≤ Real.log (N.factorial : ℝ) + N * Real.log 4 := by
  set P := (Finset.range (N + 1)).filter Nat.Prime with hP
  have hfac : Real.log (N.factorial : ℝ)
      = ∑ p ∈ P, ((N.factorial).factorization p : ℝ) * Real.log p := by
    rw [Real.log_nat_eq_sum_factorization]
    apply Finsupp.sum_of_support_subset
    · intro p hp
      rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
      simp only [hP, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le ((hp.1.dvd_factorial).1 hp.2.1), hp.1⟩
    · intro i _
      simp
  have htheta : ∑ p ∈ P, Real.log p ≤ N * Real.log 4 := by
    rw [← Real.log_prod (fun p hp => by
      have := (Finset.mem_filter.1 hp).2.pos
      positivity), ← Real.log_pow]
    apply Real.log_le_log
    · exact Finset.prod_pos fun p hp => by
        have := (Finset.mem_filter.1 hp).2.pos
        positivity
    · have h := primorial_le_four_pow N
      have h' : ((primorial N : ℕ) : ℝ) ≤ ((4 ^ N : ℕ) : ℝ) := by exact_mod_cast h
      simpa [primorial, hP, Nat.cast_prod] using h'
  rw [Finset.mul_sum, hfac]
  calc ∑ p ∈ P, (N : ℝ) * (Real.log p / p)
      ≤ ∑ p ∈ P, (((N.factorial).factorization p : ℝ) * Real.log p + Real.log p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := (Finset.mem_filter.1 hp).2
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.pos
        have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
        have hv : ((N / p : ℕ) : ℝ) ≤ ((N.factorial).factorization p : ℝ) := by
          exact_mod_cast div_le_factorization_factorial' N p hp'
        have hlt : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by
          exact_mod_cast Nat.lt_div_mul_add hp'.pos
        have hq : (N : ℝ) / p ≤ ((N.factorial).factorization p : ℝ) + 1 := by
          rw [div_le_iff₀ hp0]
          nlinarith
        calc (N : ℝ) * (Real.log p / p) = (N : ℝ) / p * Real.log p := by ring
          _ ≤ (((N.factorial).factorization p : ℝ) + 1) * Real.log p :=
            mul_le_mul_of_nonneg_right hq hlog
          _ = _ := by ring
    _ = ∑ p ∈ P, ((N.factorial).factorization p : ℝ) * Real.log p + ∑ p ∈ P, Real.log p :=
        Finset.sum_add_distrib
    _ ≤ _ := by linarith
open Finset in
private lemma log_factorial_le_stirling_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤ n * Real.log n - n + 1 + Real.log n / 2 := by
  have h1 : Real.log (Stirling.stirlingSeq n) ≤ Real.log (Stirling.stirlingSeq 1) := by
    have := Stirling.log_stirlingSeq'_antitone (Nat.zero_le (n - 1))
    simpa [Function.comp, Nat.sub_add_cancel hn] using this
  rw [Stirling.log_stirlingSeq_formula, Stirling.log_stirlingSeq_formula] at h1
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [Real.log_mul (by norm_num) hn0, Real.log_div hn0 (Real.exp_pos 1).ne', Real.log_exp] at h1
  simp only [Nat.factorial_one, Nat.cast_one, mul_one, Real.log_one, one_div, Real.log_inv,
    Real.log_exp] at h1
  linarith [h1]
end GlobalTheory.PrimeLogSum
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.PrimeLogSum
open Finset
open Finset
namespace GlobalTheory.PrimeLogSum
namespace _root_.GlobalTheory.PrimeLogSum
theorem _root_.solution : ∀ N : ℕ,
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)
      ≤ Real.log N + 2.2 := by
  intro N
  have hl2 := Real.log_two_lt_d9
  have hl3 := log_three_lt_one_point_one_one
  have hl3' : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  rcases Nat.lt_or_ge N 4 with hN | hN
  · interval_cases N <;>
      simp [Finset.sum_filter, Finset.sum_range_succ, Nat.prime_two, Nat.prime_three] <;>
      norm_num <;> linarith
  set P := (Finset.range (N + 1)).filter Nat.Prime with hP
  have hsplit : ∑ p ∈ P, Real.log p / ((p : ℝ) - 1)
      = ∑ p ∈ P, Real.log p / p + ∑ p ∈ P, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.two_le
    have h3 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h4 : (p : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  have hB : ∑ p ∈ P, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ n ∈ Finset.range (N + 1), Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro n _ _
    apply div_nonneg (Real.log_natCast_nonneg n)
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h
      exact mul_nonneg (by linarith) (by linarith)
  have hC := sum_log_div_mul_pred_add_le_const N (by omega)
  have hg : 0 ≤ (Real.log N + 4 / 3) / N :=
    div_nonneg (by linarith [Real.log_natCast_nonneg N]) (Nat.cast_nonneg N)
  have hA := mul_sum_prime_log_div_le_log_factorial_add N
  have hF := log_factorial_le_stirling_bound N (by omega)
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogN : Real.log N ≤ 0.4 * N := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (N : ℝ) / Real.exp 1 by positivity)
    rw [Real.log_div hNpos.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
    have he := Real.exp_one_gt_d9
    have h5 : (N : ℝ) / Real.exp 1 ≤ 0.4 * N := by
      rw [div_le_iff₀ (Real.exp_pos 1)]
      nlinarith
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hA' : ∑ p ∈ P, Real.log p / p ≤ Real.log N - 1 + 0.25 + 0.2 + Real.log 4 := by
    have h : (N : ℝ) * ∑ p ∈ P, Real.log p / p
        ≤ N * (Real.log N - 1 + 0.25 + 0.2 + Real.log 4) := by
      linarith
    exact le_of_mul_le_mul_left h hNpos
  rw [hsplit]
  linarith
end _root_.GlobalTheory.PrimeLogSum
end GlobalTheory.PrimeLogSum
