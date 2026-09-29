-- Prove2me | solution 1 for LubyMIS.Derandomized.technical_lemma
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:07:18.555418+00:00
-- url     : https://prove2.me/submissions/2c0a1e57-98c0-4b0e-84a7-6939d33fe8cc

import Mathlib

namespace LubyMIS.Derandomized

lemma aux_tl_beta_succ (p : ℕ → ℝ) (l : ℕ) :
    ∑ j ∈ Finset.Icc 1 (l+1), ∑ k ∈ Finset.Ioc j (l+1), p j * p k
      = ∑ j ∈ Finset.Icc 1 l, ∑ k ∈ Finset.Ioc j l, p j * p k
        + p (l+1) * ∑ j ∈ Finset.Icc 1 l, p j := by
  rw [Finset.sum_Icc_succ_top (by omega)]
  simp only [Finset.Ioc_self, Finset.sum_empty, add_zero]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Icc] at hj
  rw [Finset.sum_Ioc_succ_top hj.2]
  ring

lemma aux_tl_identity (p : ℕ → ℝ) (l : ℕ) :
    2 * ∑ j ∈ Finset.Icc 1 l, ∑ k ∈ Finset.Ioc j l, p j * p k
      = (∑ j ∈ Finset.Icc 1 l, p j) ^ 2 - ∑ j ∈ Finset.Icc 1 l, p j ^ 2 := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [aux_tl_beta_succ, Finset.sum_Icc_succ_top (by omega),
      Finset.sum_Icc_succ_top (by omega)]
    linear_combination ih

end LubyMIS.Derandomized

open LubyMIS.Derandomized

theorem solution (n : ℕ) (hn : 1 ≤ n) (p : ℕ → ℝ)
    (hanti : ∀ j k : ℕ, 1 ≤ j → j ≤ k → k ≤ n → p k ≤ p j) (hpn : 0 ≤ p n)
    (c : ℝ) (hc : 0 < c) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ n ∧
      (∑ j ∈ Finset.Icc 1 l, p j) - c * (∑ j ∈ Finset.Icc 1 l, ∑ k ∈ Finset.Ioc j l, p j * p k)
        ≥ 1 / 2 * min (∑ j ∈ Finset.Icc 1 n, p j) (1 / c) := by
  have hp0 : ∀ j, 1 ≤ j → j ≤ n → 0 ≤ p j :=
    fun j h1 h2 => le_trans hpn (hanti j n h1 h2 le_rfl)
  have hS : ∀ l, 0 ≤ ∑ j ∈ Finset.Icc 1 l, p j ^ 2 :=
    fun l => Finset.sum_nonneg (fun j _ => sq_nonneg _)
  by_cases hA : ∑ j ∈ Finset.Icc 1 n, p j ≤ 1 / c
  · refine ⟨n, hn, le_rfl, ?_⟩
    rw [min_eq_left hA]
    have hid := aux_tl_identity p n
    have hα0 : 0 ≤ ∑ j ∈ Finset.Icc 1 n, p j := by
      apply Finset.sum_nonneg
      intro j hj
      rw [Finset.mem_Icc] at hj
      exact hp0 j hj.1 hj.2
    have hcα : c * ∑ j ∈ Finset.Icc 1 n, p j ≤ 1 := by
      rw [le_div_iff₀ hc] at hA; linarith
    generalize ∑ j ∈ Finset.Icc 1 n, p j = a at *
    generalize ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Ioc j n, p j * p k = b at *
    have hSn := hS n
    generalize ∑ j ∈ Finset.Icc 1 n, p j ^ 2 = S at *
    nlinarith [mul_nonneg hα0 (sub_nonneg.2 hcα), mul_nonneg hc.le hSn]
  · push Not at hA
    rw [min_eq_right hA.le]
    classical
    have hex : ∃ m, 1 / c < ∑ j ∈ Finset.Icc 1 m, p j := ⟨n, hA⟩
    have hm : 1 / c < ∑ j ∈ Finset.Icc 1 (Nat.find hex), p j := Nat.find_spec hex
    have hmn : Nat.find hex ≤ n := Nat.find_min' hex hA
    have hcpos : 0 < 1 / c := one_div_pos.2 hc
    have hm1 : 1 ≤ Nat.find hex := by
      by_contra h
      have h0 : Nat.find hex = 0 := by omega
      rw [h0] at hm
      simp at hm
      linarith
    by_cases hm1' : Nat.find hex = 1
    · refine ⟨1, le_rfl, hn, ?_⟩
      rw [hm1'] at hm
      simp only [Finset.Icc_self, Finset.sum_singleton, Finset.Ioc_self, Finset.sum_empty,
        mul_zero, sub_zero] at hm ⊢
      linarith
    · have hmin : ¬ (1 / c < ∑ j ∈ Finset.Icc 1 (Nat.find hex - 1), p j) :=
        Nat.find_min hex (by omega)
      push Not at hmin
      refine ⟨Nat.find hex - 1, by omega, by omega, ?_⟩
      have hid := aux_tl_identity p (Nat.find hex - 1)
      have hsplit : ∑ j ∈ Finset.Icc 1 (Nat.find hex), p j
          = ∑ j ∈ Finset.Icc 1 (Nat.find hex - 1), p j + p (Nat.find hex) := by
        have he : Nat.find hex = (Nat.find hex - 1) + 1 := by omega
        conv_lhs => rw [he]
        rw [Finset.sum_Icc_succ_top (by omega), ← he]
      have hS1 : p 1 ^ 2 ≤ ∑ j ∈ Finset.Icc 1 (Nat.find hex - 1), p j ^ 2 :=
        Finset.single_le_sum (f := fun j => p j ^ 2) (fun j _ => sq_nonneg _)
          (by rw [Finset.mem_Icc]; omega)
      have hpm0 : 0 ≤ p (Nat.find hex) := hp0 _ hm1 hmn
      have hp1m : p (Nat.find hex) ≤ p 1 := hanti 1 _ le_rfl hm1 hmn
      have hq2 : p (Nat.find hex) ^ 2 ≤ p 1 ^ 2 := pow_le_pow_left₀ hpm0 hp1m 2
      rw [hsplit] at hm
      generalize p (Nat.find hex) = q at *
      generalize ∑ j ∈ Finset.Icc 1 (Nat.find hex - 1), p j = a at *
      generalize ∑ j ∈ Finset.Icc 1 (Nat.find hex - 1),
        ∑ k ∈ Finset.Ioc j (Nat.find hex - 1), p j * p k = b at *
      generalize ∑ j ∈ Finset.Icc 1 (Nat.find hex - 1), p j ^ 2 = S at *
      have hca : c * a ≤ 1 := by rw [le_div_iff₀ hc] at hmin; linarith
      have hcaq : 1 < c * (a + q) := by rw [div_lt_iff₀ hc] at hm; linarith
      have h1 : 0 ≤ 1 - c * a := by linarith
      have h2 : 1 - c * a ≤ c * q := by linarith
      have h3 : (1 - c * a) ^ 2 ≤ (c * q) ^ 2 := pow_le_pow_left₀ h1 h2 2
      have h4 : (c * q) ^ 2 ≤ c ^ 2 * S := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left (hq2.trans hS1) (sq_nonneg c)
      have key : 1 ≤ c * (2 * (a - c * b)) := by nlinarith
      have hfin : 1 / 2 * (1 / c) = 1 / (2 * c) := by field_simp
      rw [hfin, ge_iff_le, div_le_iff₀ (by positivity)]
      linarith
