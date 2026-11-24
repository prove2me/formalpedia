-- Prove2me | solution 1 for GlobalTheory.no_norm_twelve_order_sixtythree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:46.048851+00:00
-- url     : https://prove2.me/submissions/d37817a8-b470-4fb7-82d4-da9266b658de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_NoNormTwelveOrderSixtythree
import Theorems.Thm_GlobalTheory_fourier_inv_sixtythree
import Theorems.Thm_GlobalTheory_mixed_diff_sixtythree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory
private theorem apply_add_21_eq_of_fourier_vanish_order_63 (ω : ℂ) (c : ℕ → ℤ) (hω : IsPrimitiveRoot ω 63)
    (h : ∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j →
      ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) (n : ℕ) (hn : n < 42) :
    c (n + 21) = c n := by
  have hs : ∑ j ∈ Finset.range 63,
      (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * (n + 21)))
      = ∑ j ∈ Finset.range 63,
      (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * n)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    by_cases h3 : 3 ∣ j
    · have hB : ω ^ (1302 * j) = 1 := (hω.pow_eq_one_iff_dvd _).mpr (by omega)
      rw [show j * (62 * (n + 21)) = j * (62 * n) + 1302 * j by ring, pow_add, hB, mul_one]
    · rw [h j hj' (by omega) (by omega), zero_mul, zero_mul]
  have e1 := fourier_inv_sixtythree ω c hω (n + 21) (by omega)
  rw [hs, fourier_inv_sixtythree ω c hω n (by omega)] at e1
  have e2 : ((c (n + 21) : ℤ) : ℂ) = (c n : ℂ) :=
    (mul_left_cancel₀ (by norm_num : (63 : ℂ) ≠ 0) e1).symm
  exact_mod_cast e2
end GlobalTheory
end

set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 63 →
    ∑ k ∈ Finset.range 63, c k ^ 2 = 12 →
    (∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j →
      ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) → False := by
  intro ω c hω hnorm hF
  have hrel := fun m (hm : m < 53) => mixed_diff_sixtythree ω c hω hF m hm
  have hper := fun n (hn : n < 42) => apply_add_21_eq_of_fourier_vanish_order_63 ω c hω hF n hn
  have hD : ∀ m, m < 56 → c (m + 7) - c m = c (m % 3 + 7) - c (m % 3) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      by_cases h3 : m < 3
      · rw [Nat.mod_eq_of_lt h3]
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
        have e1 := hrel m' (by omega)
        have e2 := ih m' (by omega) (by omega)
        rw [show (m' + 3) % 3 = m' % 3 by omega, show m' + 3 + 7 = m' + 10 by omega]
        linarith
  have hS : ∑ k ∈ Finset.range 63, c k ^ 2 = 3 * ∑ k ∈ Finset.range 21, c k ^ 2 := by
    rw [show (63 : ℕ) = 21 + 21 + 21 from rfl, Finset.sum_range_add, Finset.sum_range_add]
    have h1 : ∑ x ∈ Finset.range 21, c (21 + x) ^ 2 = ∑ x ∈ Finset.range 21, c x ^ 2 :=
      Finset.sum_congr rfl fun x hx => by
        rw [add_comm, hper x (by have := Finset.mem_range.mp hx; omega)]
    have h2 : ∑ x ∈ Finset.range 21, c (21 + 21 + x) ^ 2 = ∑ x ∈ Finset.range 21, c x ^ 2 :=
      Finset.sum_congr rfl fun x hx => by
        have hx' := Finset.mem_range.mp hx
        rw [show 21 + 21 + x = x + 21 + 21 by omega, hper (x + 21) (by omega), hper x (by omega)]
    rw [h1, h2]
    ring
  have hcolsum : ∑ k ∈ Finset.range 21, c k ^ 2 =
      ∑ b ∈ Finset.range 7, (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2) := by
    rw [show (21 : ℕ) = 7 + 7 + 7 from rfl, Finset.sum_range_add, Finset.sum_range_add,
      Finset.sum_add_distrib, Finset.sum_add_distrib]
    have h1 : ∑ x ∈ Finset.range 7, c (7 + x) ^ 2 = ∑ x ∈ Finset.range 7, c (x + 7) ^ 2 :=
      Finset.sum_congr rfl fun x _ => by rw [add_comm]
    have h2 : ∑ x ∈ Finset.range 7, c (7 + 7 + x) ^ 2 = ∑ x ∈ Finset.range 7, c (x + 14) ^ 2 :=
      Finset.sum_congr rfl fun x _ => by rw [show 7 + 7 + x = x + 14 by omega]
    rw [h1, h2]
  have hcol : ∀ b, b < 7 → (c 7 - c 0) ^ 2 + (c 8 - c 1) ^ 2 + (c 9 - c 2) ^ 2 ≤
      3 * (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2) := by
    intro b hb
    have e1 := hD b (by omega)
    have e2 := hD (b + 7) (by omega)
    have e3 := hD (b + 14) (by omega)
    have p := hper b (by omega)
    rw [show b + 7 + 7 = b + 14 by omega] at e2
    rw [show b + 14 + 7 = b + 21 by omega, p] at e3
    have key : (c (b + 7) - c b) ^ 2 + (c (b + 14) - c (b + 7)) ^ 2 + (c b - c (b + 14)) ^ 2 ≤
        3 * (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2) := by
      nlinarith [sq_nonneg (c b + c (b + 7) + c (b + 14))]
    rw [e1, e2, e3] at key
    have hb3 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases hb3 with h | h | h
    · rw [show (b + 7) % 3 = 1 by omega, show (b + 14) % 3 = 2 by omega, h] at key
      norm_num at key
      linarith
    · rw [show (b + 7) % 3 = 2 by omega, show (b + 14) % 3 = 0 by omega, h] at key
      norm_num at key
      linarith
    · rw [show (b + 7) % 3 = 0 by omega, show (b + 14) % 3 = 1 by omega, h] at key
      norm_num at key
      linarith
  rw [hS] at hnorm
  have hS21 : ∑ k ∈ Finset.range 21, c k ^ 2 = 4 := by omega
  have hΔ : 7 * ((c 7 - c 0) ^ 2 + (c 8 - c 1) ^ 2 + (c 9 - c 2) ^ 2) ≤ 12 := by
    have hle := Finset.sum_le_sum (s := Finset.range 7) fun b hb => hcol b (Finset.mem_range.mp hb)
    rw [← Finset.mul_sum, ← hcolsum, hS21] at hle
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    push_cast at hle
    linarith
  have hsum0 : (c 7 - c 0) + (c 8 - c 1) + (c 9 - c 2) = 0 := by
    have e2 := hD 7 (by omega)
    have e3 := hD 14 (by omega)
    have p := hper 0 (by omega)
    norm_num at e2 e3 p
    linarith
  have hzero : c 7 - c 0 = 0 ∧ c 8 - c 1 = 0 ∧ c 9 - c 2 = 0 := by
    generalize c 7 - c 0 = x at hΔ hsum0 ⊢
    generalize c 8 - c 1 = y at hΔ hsum0 ⊢
    generalize c 9 - c 2 = z at hΔ hsum0 ⊢
    have hz : z = -x - y := by linarith
    subst hz
    have h14 : 14 * (x ^ 2 + x * y + y ^ 2) ≤ 12 := by nlinarith
    have hq : x ^ 2 + x * y + y ^ 2 ≤ 0 := by omega
    have hy2 : y ^ 2 ≤ 0 := by nlinarith [sq_nonneg (2 * x + y)]
    have hy : y = 0 := (pow_eq_zero_iff two_ne_zero).mp (le_antisymm hy2 (sq_nonneg y))
    subst hy
    have hx2 : x ^ 2 ≤ 0 := by nlinarith
    have hx : x = 0 := (pow_eq_zero_iff two_ne_zero).mp (le_antisymm hx2 (sq_nonneg x))
    subst hx
    norm_num
  have hp7 : ∀ r, r < 3 → c (r + 7) = c r := by
    intro r hr
    interval_cases r <;> norm_num <;> omega
  have hcolc : ∀ b, b < 7 → c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2 = 3 * c b ^ 2 := by
    intro b hb
    have e1 := hD b (by omega)
    have e2 := hD (b + 7) (by omega)
    rw [show b + 7 + 7 = b + 14 by omega] at e2
    rw [hp7 (b % 3) (Nat.mod_lt _ (by norm_num))] at e1
    rw [hp7 ((b + 7) % 3) (Nat.mod_lt _ (by norm_num))] at e2
    have h1 : c (b + 7) = c b := by linarith
    have h2 : c (b + 14) = c b := by linarith
    rw [h1, h2]
    ring
  have h3 : ∑ b ∈ Finset.range 7, (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2) =
      3 * ∑ b ∈ Finset.range 7, c b ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b hb => hcolc b (Finset.mem_range.mp hb)
  rw [hcolsum, h3] at hS21
  omega
end GlobalTheory
