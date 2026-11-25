-- Prove2me | solution 1 for GlobalTheory.PrimeRecip.inv_five_log_le_sum_inv_primes_of_large
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:11.252372+00:00
-- url     : https://prove2.me/submissions/683a9d7f-54be-4dd9-a862-8d7e67b820b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvFiveLogLeSumInvPrimes
import Theorems.Thm_GlobalTheory_PrimeRecip_three_mul_primeCounting_le
import Theorems.Thm_GlobalTheory_PrimeRecip_centralBinom_le_pow_primeCounting

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
theorem _root_.solution (N : ℕ) (hN : 16900 ≤ N) :
    1 / (5 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p := by
  set U := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) with hU
  obtain ⟨n, hn⟩ : ∃ n, n = N / 2 := ⟨_, rfl⟩
  set T := (Finset.range (2 * n + 1)).filter (fun p => p.Prime ∧ n < p) with hT
  have hcard : T.card ≤ U.card + 3 := by
    have hsub : T ⊆ U ∪ {N - 2, N - 1, N} := by
      intro x hx
      obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hx
      rw [Finset.mem_range] at h1
      by_cases h : x + 3 ≤ N
      · exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2
          ⟨Finset.mem_range.2 (by omega), h2, by omega, h⟩))
      · refine Finset.mem_union.2 (Or.inr ?_)
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    exact Nat.add_le_add_left Finset.card_le_three _
  have h1 := Nat.four_pow_lt_mul_centralBinom n (by omega)
  have h2 := centralBinom_le_pow_primeCounting n (by omega)
  rw [← hT] at h2
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt N := ⟨_, rfl⟩
  have hs1 : s * s ≤ N := hs ▸ Nat.sqrt_le N
  have hs2 : N < (s + 1) * (s + 1) := hs ▸ Nat.lt_succ_sqrt N
  have hs3 : 130 ≤ s := by
    by_contra h
    have : s + 1 ≤ 130 := by omega
    have := Nat.mul_le_mul this this
    omega
  obtain ⟨K, hK⟩ : ∃ K, K = Nat.primeCounting (Nat.sqrt (2 * n)) := ⟨_, rfl⟩
  rw [← hK] at h2
  have hK3 : 3 * K ≤ s + 9 := by
    have a : K ≤ Nat.primeCounting s :=
      hK ▸ Nat.monotone_primeCounting (hs ▸ Nat.sqrt_le_sqrt (by omega))
    have b := three_mul_primeCounting_le s (by omega)
    omega
  obtain ⟨m, hm⟩ : ∃ m, m = n - 2 * n / 3 := ⟨_, rfl⟩
  have h3 : 4 ^ m ≤ N ^ (K + U.card + 4) := by
    have hNpos : 1 ≤ N := by omega
    have e : 4 ^ n = 4 ^ m * 4 ^ (2 * n / 3) := by
      rw [← pow_add]; congr 1; omega
    have a1 : (2 * n) ^ K ≤ N ^ K := Nat.pow_le_pow_left (by omega) _
    have a2 : (2 * n) ^ T.card ≤ N ^ (U.card + 3) :=
      (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right hNpos hcard)
    have a3 : 4 ^ m * 4 ^ (2 * n / 3) ≤ N ^ (K + U.card + 4) * 4 ^ (2 * n / 3) := by
      rw [← e]
      calc 4 ^ n ≤ n * n.centralBinom := h1.le
        _ ≤ N * (N ^ K * 4 ^ (2 * n / 3) * N ^ (U.card + 3)) :=
          Nat.mul_le_mul (by omega) (h2.trans (Nat.mul_le_mul (Nat.mul_le_mul_right _ a1) a2))
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right a3 (by positivity)
  have hNR : (16900 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have h4 : (m : ℝ) * Real.log 4 ≤ (K + U.card + 4) * Real.log N := by
    have : ((4 : ℝ)) ^ m ≤ (N : ℝ) ^ (K + U.card + 4) := by exact_mod_cast h3
    have := Real.log_le_log (by positivity) this
    rw [Real.log_pow, Real.log_pow] at this
    exact_mod_cast this
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hmR : (N : ℝ) ≤ 6 * m + 1 := by
    have : N ≤ 6 * m + 1 := by omega
    exact_mod_cast this
  have hsR : (130 : ℝ) ≤ s := by exact_mod_cast hs3
  have hs1R : (s : ℝ) * s ≤ N := by exact_mod_cast hs1
  have hs2R : (N : ℝ) ≤ (s + 1) * (s + 1) := by exact_mod_cast hs2.le
  have hK3R : 3 * (K : ℝ) ≤ s + 9 := by exact_mod_cast hK3
  have hLle : Real.log N ≤ (s + 1) / 64 + 7.70407 := by
    have b1 : Real.log N ≤ 2 * Real.log (s + 1) := by
      have := Real.log_le_log (by linarith) hs2R
      rw [Real.log_mul (by linarith) (by linarith)] at this
      linarith
    have b2 : Real.log ((s + 1) / 2 ^ 7) ≤ (s + 1) / 2 ^ 7 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by linarith) (by norm_num), Real.log_pow] at b2
    push_cast at b2
    linarith
  have h5 : (N : ℝ) ≤ U.card * (5 * Real.log N) := by
    have c1 : ((s : ℝ) + 21) * Real.log N ≤ (s + 21) * ((s + 1) / 64 + 7.70407) :=
      mul_le_mul_of_nonneg_left hLle (by linarith)
    have c2 : (m : ℝ) * 1.386294 ≤ m * Real.log 4 :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    have c3 : 130 * (s : ℝ) ≤ s * s := mul_le_mul_of_nonneg_right hsR (by linarith)
    have c4 : 3 * (K : ℝ) * Real.log N ≤ (s + 9) * Real.log N :=
      mul_le_mul_of_nonneg_right hK3R hL.le
    nlinarith
  calc 1 / (5 * Real.log N) ≤ (U.card : ℝ) * (1 / N) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by linarith)]
        linarith
    _ = ∑ _p ∈ U, (1 : ℝ) / N := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨-, hp1, -, hp2⟩ := Finset.mem_filter.1 hp
        have : (0 : ℝ) < p := by exact_mod_cast hp1.pos
        have h' : (p : ℝ) ≤ N := by exact_mod_cast (by omega : p ≤ N)
        exact one_div_le_one_div_of_le this h'
end GlobalTheory.PrimeRecip
