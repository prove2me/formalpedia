-- Prove2me | solution 1 for GlobalTheory.PrimeRecip.okIv_sound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:33:36.426936+00:00
-- url     : https://prove2.me/submissions/2dacb074-b103-4bbb-ab89-51d2702b1605

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvFiveLogLeSumInvPrimes
import Theorems.Thm_GlobalTheory_PrimeRecip_prime_of_check
import Theorems.Thm_GlobalTheory_PrimeRecip_sortedB_pairwise

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
theorem _root_.solution {a b j c : ℕ} {L : List ℕ} (h : okIv a b j c L = true) (N : ℕ) (haN : a ≤ N)
    (hNb : N < b) :
    1 / (5 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p := by
  simp only [okIv, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hall, hsort⟩, hj⟩, hc0⟩, hk⟩ := h
  have hnd : L.Nodup := (sortedB_pairwise L hsort).imp (fun h => ne_of_lt h)
  have hcard : L.toFinset.card = L.length := List.toFinset_card_of_nodup hnd
  have hsub : L.toFinset ⊆
      (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) := by
    intro p hp
    rw [List.mem_toFinset] at hp
    obtain ⟨⟨⟨⟨⟨h2, h3⟩, h4⟩, h5⟩, h6⟩, -⟩ := hall p hp
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, prime_of_check h2 h3 h4, by omega, by omega⟩
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc0
  have hkR : (c : ℝ) * 10 ^ 10 ≤ 5 * L.length * j * 6931471803 := by exact_mod_cast hk
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; simp at hk; omega
    · exact h0
  have h2j : 2 ≤ N := by
    have : 2 ^ 1 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
    omega
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast h2j
  have hlogN : (j : ℝ) * Real.log 2 ≤ Real.log N := by
    have h2jR : ((2 : ℝ)) ^ j ≤ N := by exact_mod_cast (hj.trans haN)
    have := Real.log_le_log (by positivity) h2jR
    rwa [Real.log_pow] at this
  have hl2 := Real.log_two_gt_d9
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  calc 1 / (5 * Real.log N) ≤ (L.length : ℝ) * (1 / c) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) hcR]
        have e1 : (L.length : ℝ) * (j * 0.6931471803) ≤ L.length * (j * Real.log 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl2.le (by positivity))
            (by positivity)
        have e2 : (L.length : ℝ) * (j * Real.log 2) ≤ L.length * Real.log N :=
          mul_le_mul_of_nonneg_left hlogN (by positivity)
        nlinarith
    _ = ∑ _p ∈ L.toFinset, (1 : ℝ) / c := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ ≤ ∑ p ∈ L.toFinset, (1 : ℝ) / p := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [List.mem_toFinset] at hp
        obtain ⟨⟨⟨⟨⟨h2, -⟩, -⟩, -⟩, -⟩, h7⟩ := hall p hp
        have : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
        exact one_div_le_one_div_of_le this (by exact_mod_cast h7)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
end GlobalTheory.PrimeRecip
