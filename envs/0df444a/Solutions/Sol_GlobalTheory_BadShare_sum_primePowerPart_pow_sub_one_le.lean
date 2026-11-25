-- Prove2me | solution 1 for GlobalTheory.BadShare.sum_primePowerPart_pow_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:38:02.312079+00:00
-- url     : https://prove2.me/submissions/cd288abf-d990-49d4-86b5-de3d78e0df3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumPrimePowerPartPowSubOneLe
import Theorems.Thm_GlobalTheory_BadShare_sum_prime_pow_le_of_dvd
import Theorems.Thm_GlobalTheory_BadShare_pow_padicValNat_pow_sub_one_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution :
    ∀ g d : ℕ, 2 ≤ g → 4 ∣ g - 1 → 2 ≤ d → (∑ l ∈ (g ^ d - 1).primeFactors, ((l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ)) ≤ d * ((g : ℝ) - 1) + ((g : ℝ) ^ d - 1) / ((g : ℝ) - 1) := by
  intro g d hg h4 hd
  set N := g ^ d - 1 with hN
  have hd0 : d ≠ 0 := by omega
  have hg1 : g - 1 ≠ 0 := by omega
  have hdiv : g - 1 ∣ N := by simpa using Nat.sub_dvd_pow_sub_pow g 1 d
  have hv : ∀ l ∈ N.primeFactors, padicValNat l N ≠ 0 := by
    intro l hl
    obtain ⟨hlp, hlN, hN0⟩ := Nat.mem_primeFactors.mp hl
    have := Fact.mk hlp
    exact Nat.one_le_iff_ne_zero.mp (one_le_padicValNat_of_dvd hN0 hlN)
  have hnat : ∑ l ∈ N.primeFactors, l ^ padicValNat l N ≤ d * (g - 1) + N / (g - 1) := by
    rw [← Finset.sum_filter_add_sum_filter_not N.primeFactors (fun l => l ∣ g - 1)]
    refine add_le_add ?_ ?_
    · refine sum_prime_pow_le_of_dvd _ _ _ (mul_ne_zero hd0 hg1)
        (fun l hl => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hl).1).1)
        (fun l hl => hv l (Finset.mem_filter.mp hl).1) (fun l hl => ?_)
      obtain ⟨hl1, hlg⟩ := Finset.mem_filter.mp hl
      exact pow_padicValNat_pow_sub_one_dvd g d l hg h4 hd0 (Nat.mem_primeFactors.mp hl1).1 hlg
    · have hQ0 : N / (g - 1) ≠ 0 := by
        intro h0
        have hm := Nat.div_mul_cancel hdiv
        rw [h0, zero_mul] at hm
        have : 1 < g ^ d := Nat.one_lt_pow hd0 (by omega)
        omega
      refine sum_prime_pow_le_of_dvd _ _ _ hQ0
        (fun l hl => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hl).1).1)
        (fun l hl => hv l (Finset.mem_filter.mp hl).1) (fun l hl => ?_)
      obtain ⟨hl1, hlg⟩ := Finset.mem_filter.mp hl
      obtain ⟨hlp, -, -⟩ := Nat.mem_primeFactors.mp hl1
      have hcop : Nat.Coprime (l ^ padicValNat l N) (g - 1) :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hlp).mpr hlg)
      refine hcop.dvd_of_dvd_mul_right ?_
      rw [Nat.div_mul_cancel hdiv]
      exact pow_padicValNat_dvd
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hcast_g1 : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ g)]
    simp
  have hcast_N : ((N : ℕ) : ℝ) = (g : ℝ) ^ d - 1 := by
    rw [hN, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
    simp
  have hcast_Q : ((N / (g - 1) : ℕ) : ℝ) = ((g : ℝ) ^ d - 1) / ((g : ℝ) - 1) := by
    rw [Nat.cast_div hdiv (by rw [hcast_g1]; linarith), hcast_N, hcast_g1]
  calc (∑ l ∈ N.primeFactors, ((l ^ padicValNat l N : ℕ) : ℝ))
        = ((∑ l ∈ N.primeFactors, l ^ padicValNat l N : ℕ) : ℝ) := by rw [Nat.cast_sum]
    _ ≤ ((d * (g - 1) + N / (g - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = _ := by rw [Nat.cast_add, Nat.cast_mul, hcast_g1, hcast_Q]
end GlobalTheory.BadShare
