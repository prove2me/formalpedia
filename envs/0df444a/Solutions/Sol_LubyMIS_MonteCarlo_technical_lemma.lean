-- Prove2me | solution 1 for LubyMIS.MonteCarlo.technical_lemma
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:40:48.71391+00:00
-- url     : https://prove2.me/submissions/455ed6ee-14c6-4007-9d63-458e2fda5f1b

import Mathlib



namespace LubyMIS.MonteCarlo

theorem tl_alpha_succ (p : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Finset.Icc 1 (m+1), p j = (∑ j ∈ Finset.Icc 1 m, p j) + p (m+1) := by
  rw [Finset.sum_Icc_succ_top (by omega)]

theorem tl_beta_succ (p : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Finset.Icc 1 (m+1), ∑ k ∈ Finset.Ioc j (m+1), p j * p k =
      (∑ j ∈ Finset.Icc 1 m, ∑ k ∈ Finset.Ioc j m, p j * p k)
        + p (m+1) * ∑ j ∈ Finset.Icc 1 m, p j := by
  rw [Finset.sum_Icc_succ_top (by omega)]
  have h0 : Finset.Ioc (m+1) (m+1) = ∅ := by simp
  rw [h0, Finset.sum_empty, add_zero, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_Icc] at hj
  rw [Finset.sum_Ioc_succ_top (by omega : j ≤ m)]; ring

theorem tl_beta_le (p : ℕ → ℝ) (n : ℕ) (hp : ∀ j, 1 ≤ j → j ≤ n → 0 ≤ p j) :
    ∀ m, m ≤ n → 2 * (∑ j ∈ Finset.Icc 1 m, ∑ k ∈ Finset.Ioc j m, p j * p k)
      ≤ (∑ j ∈ Finset.Icc 1 m, p j) ^ 2 ∧ 0 ≤ ∑ j ∈ Finset.Icc 1 m, p j := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hpm := hp (m+1) (by omega) hm
    rw [tl_beta_succ, tl_alpha_succ]
    constructor
    · nlinarith
    · linarith

theorem technical_lemma_core (n : ℕ) (hn : 1 ≤ n) (p : ℕ → ℝ)
    (hanti : ∀ j k : ℕ, 1 ≤ j → j ≤ k → k ≤ n → p k ≤ p j) (hpn : 0 ≤ p n)
    (c : ℝ) (hc : 0 < c) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ n ∧
      (∑ j ∈ Finset.Icc 1 l, p j) - c * (∑ j ∈ Finset.Icc 1 l, ∑ k ∈ Finset.Ioc j l, p j * p k)
        ≥ 1 / 2 * min (∑ j ∈ Finset.Icc 1 n, p j) (1 / c) := by
  have hp : ∀ j, 1 ≤ j → j ≤ n → 0 ≤ p j := fun j h1 h2 => le_trans hpn (hanti j n h1 h2 le_rfl)
  have hB := tl_beta_le p n hp
  set α : ℕ → ℝ := fun l => ∑ j ∈ Finset.Icc 1 l, p j with hα
  set β : ℕ → ℝ := fun l => ∑ j ∈ Finset.Icc 1 l, ∑ k ∈ Finset.Ioc j l, p j * p k with hβ
  show ∃ l : ℕ, 1 ≤ l ∧ l ≤ n ∧ α l - c * β l ≥ 1 / 2 * min (α n) (1 / c)
  have hB' : ∀ m, m ≤ n → 2 * β m ≤ (α m)^2 ∧ 0 ≤ α m := hB
  have hαs : ∀ m, α (m+1) = α m + p (m+1) := fun m => tl_alpha_succ p m
  have hβs : ∀ m, β (m+1) = β m + p (m+1) * α m := fun m => tl_beta_succ p m
  clear_value α β
  have hcinv : c * (1 / c) = 1 := by field_simp
  by_cases hex : ∃ m, m < n ∧ 1 ≤ c * α (m+1)
  · classical
    let m := Nat.find hex
    have hm : m < n ∧ 1 ≤ c * α (m+1) := Nat.find_spec hex
    have hmin : c * α m < 1 := by
      rcases Nat.eq_zero_or_eq_succ_pred m with h0 | h0
      · have : α 0 = 0 := by simp [hα]
        rw [h0, this]; simp
      · have hlt : m - 1 < m := by omega
        have := Nat.find_min hex hlt
        push_neg at this
        have h' := this (by omega)
        rw [h0]; simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel (show 1 ≤ m by omega)] using h'
    refine ⟨m+1, by omega, by omega, ?_⟩
    obtain ⟨hb, ha⟩ := hB' m (by omega)
    have hpm := hp (m+1) (by omega) (by omega)
    rw [hαs, hβs] at *
    have key : c * (α m + p (m+1) - c * (β m + p (m+1) * α m)) ≥ 1/2 := by
      have e1 : c * α m - c * c * β m ≥ c * α m - (c * α m)^2 / 2 := by nlinarith
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - c * α m) (by linarith : (0:ℝ) ≤ 1 - c * α m)]
    have : α m + p (m+1) - c * (β m + p (m+1) * α m) ≥ 1 / 2 * (1 / c) := by
      rw [ge_iff_le, ← mul_le_mul_iff_of_pos_left hc]
      calc c * (1/2 * (1/c)) = 1/2 := by field_simp
        _ ≤ _ := key
    exact le_trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)) this
  · push_neg at hex
    have hlt : c * α n < 1 := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n-1, by omega⟩
      exact hex k (by omega)
    refine ⟨n, hn, le_rfl, ?_⟩
    obtain ⟨hb, ha⟩ := hB' n le_rfl
    have : α n - c * β n ≥ 1/2 * α n := by nlinarith
    exact le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)) this

end LubyMIS.MonteCarlo

open LubyMIS.MonteCarlo


theorem solution (n : ℕ) (hn : 1 ≤ n) (p : ℕ → ℝ)
    (hanti : ∀ j k : ℕ, 1 ≤ j → j ≤ k → k ≤ n → p k ≤ p j) (hpn : 0 ≤ p n)
    (c : ℝ) (hc : 0 < c) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ n ∧
      (∑ j ∈ Finset.Icc 1 l, p j) - c * (∑ j ∈ Finset.Icc 1 l, ∑ k ∈ Finset.Ioc j l, p j * p k)
        ≥ 1 / 2 * min (∑ j ∈ Finset.Icc 1 n, p j) (1 / c) := by
  exact technical_lemma_core n hn p hanti hpn c hc
