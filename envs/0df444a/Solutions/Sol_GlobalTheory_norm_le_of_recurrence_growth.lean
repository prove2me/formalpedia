-- Prove2me | solution 1 for GlobalTheory.norm_le_of_recurrence_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:27:24.975843+00:00
-- url     : https://prove2.me/submissions/66dcbe16-ffc5-4b93-9500-b5d5c33a8b3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_NormLeOfRecurrenceGrowth

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
theorem _root_.solution : ∀ (β : Multiset ℂ) (a : ℕ → ℂ) (C B : ℝ) (m : ℕ), 0 < B → a 0 = 1 → (∀ n, 1 ≤ n → ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) = 0) → (∀ n, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ m * B ^ n) → ∀ b ∈ β, ‖b‖ ≤ B := by
  intro β a C B m hB ha0 hrec hgrow b hb
  by_contra hlt
  push_neg at hlt
  have hb0 : b ≠ 0 := by
    intro h; rw [h, norm_zero] at hlt; linarith
  set X : ℂ := b⁻¹ with hX
  have hXn : ‖X‖ = ‖b‖⁻¹ := norm_inv b
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  set r : ℝ := B * ‖X‖ with hr
  have hrpos : 0 < r := by rw [hr, hXn]; positivity
  have hr1 : r < 1 := by
    rw [hr, hXn, ← div_eq_mul_inv, div_lt_one hbpos]; exact hlt
  have hes : ∀ k, Multiset.card β < k → β.esymm k = 0 := by
    intro k hk
    simp [Multiset.esymm, Multiset.powersetCard_eq_empty _ hk]
  set d := Multiset.card β with hd
  set p : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * β.esymm k * X ^ k with hp
  have hpz : ∀ k ∉ Finset.range (d + 1), p k = 0 := by
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [hp, hes k (by omega)]
  have hpsum : ∑ k ∈ Finset.range (d + 1), p k = 0 := by
    have h1 := congrArg (Polynomial.eval b) (Multiset.prod_X_sub_X_eq_sum_esymm β)
    rw [Polynomial.eval_multiset_prod, Polynomial.eval_finset_sum] at h1
    have hz : (Multiset.map (Polynomial.eval b)
        (Multiset.map (fun t => Polynomial.X - Polynomial.C t) β)).prod = 0 := by
      apply Multiset.prod_eq_zero
      rw [Multiset.map_map]
      exact Multiset.mem_map.mpr ⟨b, hb, by simp⟩
    rw [hz] at h1
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one,
      Polynomial.eval_C, Polynomial.eval_X] at h1
    have h2 : ∑ k ∈ Finset.range (d + 1), p k
        = X ^ d * ∑ j ∈ Finset.range (d + 1), (-1 : ℂ) ^ j * (β.esymm j * b ^ (d - j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkd : k ≤ d := by rw [Finset.mem_range] at hk; omega
      have hXb : X ^ (d - k) * b ^ (d - k) = 1 := by
        rw [← mul_pow, hX, inv_mul_cancel₀ hb0, one_pow]
      have : X ^ d = X ^ k * X ^ (d - k) := by rw [← pow_add, Nat.add_sub_cancel' hkd]
      simp only [hp]
      rw [this]
      linear_combination (-1 : ℂ) ^ k * β.esymm k * X ^ k * hXb.symm
    rw [h2, ← h1, mul_zero]
  have hpsumm : Summable (fun k => ‖p k‖) :=
    summable_of_ne_finset_zero (s := Finset.range (d + 1)) (fun k hk => by simp [hpz k hk])
  have hptsum : ∑' k, p k = 0 := by
    rw [tsum_eq_sum (s := Finset.range (d + 1)) hpz, hpsum]
  set q : ℕ → ℂ := fun n => a n * X ^ n with hq
  have hgeo : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ m * r ^ n) := by
    have h0 : Summable (fun n : ℕ => (n : ℝ) ^ m * r ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one m (by rw [Real.norm_eq_abs, abs_of_pos hrpos]; exact hr1)
    have h1 := (summable_nat_add_iff 1).mpr h0
    have h2 := h1.mul_left r⁻¹
    refine h2.congr (fun n => ?_)
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  have hqsumm : Summable (fun n => ‖q n‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hgeo.mul_left C)
    simp only [hq, norm_mul, norm_pow]
    calc ‖a n‖ * ‖X‖ ^ n ≤ C * ((n : ℝ) + 1) ^ m * B ^ n * ‖X‖ ^ n :=
          mul_le_mul_of_nonneg_right (hgrow n) (by positivity)
      _ = C * (((n : ℝ) + 1) ^ m * r ^ n) := by rw [hr, mul_pow]; ring
  have hcauchy := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hpsumm hqsumm
  rw [hptsum, zero_mul] at hcauchy
  have hterm : ∀ n, ∑ k ∈ Finset.range (n + 1), p k * q (n - k)
      = X ^ n * ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) := by
    intro n
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by rw [Finset.mem_range] at hk; omega
    have : X ^ n = X ^ k * X ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hkn]
    simp only [hp, hq]
    rw [this]; ring
  have hone : ∑' n, ∑ k ∈ Finset.range (n + 1), p k * q (n - k) = 1 := by
    rw [tsum_eq_single 0]
    · simp [hp, hq, ha0, Multiset.esymm, Multiset.powersetCard_zero_left]
    · intro n hn
      rw [hterm n, hrec n (Nat.one_le_iff_ne_zero.mpr hn), mul_zero]
  rw [hone] at hcauchy
  exact zero_ne_one hcauchy
end GlobalTheory
