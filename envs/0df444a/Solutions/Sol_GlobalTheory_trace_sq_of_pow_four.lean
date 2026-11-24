-- Prove2me | solution 1 for GlobalTheory.trace_sq_of_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:37:45.015551+00:00
-- url     : https://prove2.me/submissions/fc89d748-088e-4a12-b6ad-8afdff7d4898

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Theorems.Thm_GlobalTheory_exists_nat_trace_of_pow_four

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open GlobalTheory
variable {A : Type*} [Fintype A] [DecidableEq A]
namespace GlobalTheory
theorem _root_.solution {U : Matrix A A ℂ} (hU : U ^ 4 = 1) (h2 : (U ^ 2).trace = 1)
    (h13 : U.trace * (U ^ 3).trace = 1) (hodd : Odd (Fintype.card A)) :
    U.trace ^ 2 = (ZMod.χ₄ (Fintype.card A : ZMod 4) : ℤ) := by
  obtain ⟨r, hr⟩ := exists_nat_trace_of_pow_four hU
  obtain ⟨t, ht⟩ := exists_nat_trace_of_pow_four (V := Complex.I • U) (by
    rw [smul_pow, hU, Complex.I_pow_four, one_smul])
  simp only [smul_pow, trace_smul, smul_eq_mul, h2, Complex.I_sq, Complex.I_pow_three] at hr ht
  set a := U.trace
  set b := (U ^ 3).trace
  set D := Fintype.card A
  have hm : a + b = ((4 * r - D - 1 : ℤ) : ℂ) := by push_cast; linear_combination hr
  have hn : Complex.I * (a - b) = ((4 * t - D + 1 : ℤ) : ℂ) := by push_cast; linear_combination ht
  have hmn : (4 * r - D - 1 : ℤ) ^ 2 + (4 * t - D + 1 : ℤ) ^ 2 = 4 := by
    have : (((4 * r - D - 1 : ℤ) ^ 2 + (4 * t - D + 1 : ℤ) ^ 2 : ℤ) : ℂ) = ((4 : ℤ) : ℂ) := by
      rw [Int.cast_add, Int.cast_pow, Int.cast_pow, ← hm, ← hn, mul_pow, Complex.I_sq]
      push_cast
      linear_combination 4 * h13
    exact_mod_cast this
  rcases Nat.odd_mod_four_iff.1 (Nat.odd_iff.1 hodd) with h | h
  · have h0 : (4 * t - D + 1 : ℤ) = 0 := by
      obtain ⟨k, hk⟩ : ∃ k : ℤ, (4 * t - D + 1 : ℤ) = 4 * k := ⟨t - D / 4, by omega⟩
      rw [hk] at hmn ⊢
      have : k = 0 := by nlinarith [sq_nonneg (4 * r - D - 1 : ℤ), sq_nonneg k, sq_nonneg (k - 1), sq_nonneg (k+1), Int.one_le_abs (z := k), sq_abs k]
      simp [this]
    rw [h0] at hn
    have hab : a = b := by simpa [sub_eq_zero] using hn
    rw [ZMod.χ₄_nat_one_mod_four h, pow_two]
    simpa [← hab] using h13
  · have h0 : (4 * r - D - 1 : ℤ) = 0 := by
      obtain ⟨k, hk⟩ : ∃ k : ℤ, (4 * r - D - 1 : ℤ) = 4 * k := ⟨r - D / 4 - 1, by omega⟩
      rw [hk] at hmn ⊢
      have : k = 0 := by nlinarith [sq_nonneg (4 * t - D + 1 : ℤ), sq_nonneg k]
      simp [this]
    rw [h0] at hm
    rw [ZMod.χ₄_nat_three_mod_four h]
    push_cast at hm ⊢
    linear_combination a * hm - h13
end GlobalTheory
