-- Prove2me | solution 1 for LNChannels.Exact.general_solution
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:01:20.977679+00:00
-- url     : https://prove2.me/submissions/91e81d59-1880-49e7-8498-51cef5e11a44

import Mathlib
import Definitions.Def_LNChannels_Exact_alphaPlus
import Definitions.Def_LNChannels_Exact_alphaMinus

set_option autoImplicit false
open LNChannels.Exact

namespace LNH

lemma root_facts (l1 l2 r : ℝ) (h1 : 0 < l1) (h2 : 0 < l2) (hr : 0 < r) :
    0 < alphaMinus l1 l2 r ∧ alphaMinus l1 l2 r < 1 ∧ 1 < alphaPlus l1 l2 r ∧
    l2 * alphaMinus l1 l2 r ^ 2 - (l1 + l2 + r) * alphaMinus l1 l2 r + l1 = 0 ∧
    l2 * alphaPlus l1 l2 r ^ 2 - (l1 + l2 + r) * alphaPlus l1 l2 r + l1 = 0 := by
  have hD : 0 < (l2 - l1) ^ 2 + r ^ 2 + 2 * r * (l2 + l1) := by positivity
  have hd2 : Real.sqrt ((l2 - l1) ^ 2 + r ^ 2 + 2 * r * (l2 + l1)) ^ 2
      = (l2 - l1) ^ 2 + r ^ 2 + 2 * r * (l2 + l1) := Real.sq_sqrt hD.le
  have hdpos : 0 < Real.sqrt ((l2 - l1) ^ 2 + r ^ 2 + 2 * r * (l2 + l1)) := Real.sqrt_pos.2 hD
  unfold alphaMinus alphaPlus
  generalize Real.sqrt ((l2 - l1) ^ 2 + r ^ 2 + 2 * r * (l2 + l1)) = d at hd2 hdpos ⊢
  have hs : (l1 + l2 + r) ^ 2 - d ^ 2 = 4 * l1 * l2 := by rw [hd2]; ring
  have hsd : d < l1 + l2 + r := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact div_pos (by linarith) (by positivity)
  · rw [div_lt_one (by positivity)]
    by_contra hcon
    push_neg at hcon
    nlinarith
  · rw [lt_div_iff₀ (by positivity)]
    by_contra hcon
    push_neg at hcon
    nlinarith
  · have : l2 * ((l1 + l2 + r - d) / (2 * l2)) ^ 2 - (l1 + l2 + r) * ((l1 + l2 + r - d) / (2 * l2)) + l1
        = (d ^ 2 - (l1 + l2 + r) ^ 2 + 4 * l1 * l2) / (4 * l2) := by
      field_simp; ring
    rw [this]; rw [div_eq_zero_iff]; left; linarith
  · have : l2 * ((l1 + l2 + r + d) / (2 * l2)) ^ 2 - (l1 + l2 + r) * ((l1 + l2 + r + d) / (2 * l2)) + l1
        = (d ^ 2 - (l1 + l2 + r) ^ 2 + 4 * l1 * l2) / (4 * l2) := by
      field_simp; ring
    rw [this]; rw [div_eq_zero_iff]; left; linarith

lemma zpow_rec (l1 l2 r α : ℝ) (hα : 0 < α) (hroot : l2 * α ^ 2 - (l1 + l2 + r) * α + l1 = 0) (n : ℤ) :
    α ^ n * (r + l2 + l1) = l2 * α ^ (n + 1) + l1 * α ^ (n - 1) := by
  rw [zpow_add_one₀ hα.ne', zpow_sub_one₀ hα.ne']
  have hα' : α ≠ 0 := hα.ne'
  have hdm : α ^ n / α * α = α ^ n := div_mul_cancel₀ _ hα'
  apply mul_right_cancel₀ hα'
  linear_combination (-(α ^ n)) * hroot - l1 * hdm

lemma gen_sol_core (lam₁ lam₂ r : ℝ) (l₁ l₂ : ℕ)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hr : 0 < r) (hl : 1 ≤ l₁ + l₂)
    (a b : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (hab : a < b)
    (hra : lam₂ * a ^ 2 - (lam₁ + lam₂ + r) * a + lam₁ = 0)
    (hrb : lam₂ * b ^ 2 - (lam₁ + lam₂ + r) * b + lam₁ = 0)
    (J : ℤ → ℝ) :
    (∀ n : ℤ, -(l₁ : ℤ) < n → n < (l₂ : ℤ) →
        J n = ((l₁ : ℝ) + l₂) * (r / (r + lam₂ + lam₁))
              + J (n + 1) * (lam₂ / (r + lam₂ + lam₁))
              + J (n - 1) * (lam₁ / (r + lam₂ + lam₁))) ↔
      ∃ k₁ k₂ : ℝ, ∀ n : ℤ, -(l₁ : ℤ) ≤ n → n ≤ (l₂ : ℤ) →
        J n = (l₁ : ℝ) + l₂ + k₁ * a ^ n + k₂ * b ^ n := by
  have hS : 0 < r + lam₂ + lam₁ := by positivity
  have ra := zpow_rec lam₁ lam₂ r a ha0 hra
  have rb := zpow_rec lam₁ lam₂ r b hb0 hrb
  constructor
  · intro h
    have hK : ∀ n : ℤ, -(l₁ : ℤ) < n → n < (l₂ : ℤ) →
        (J n - ((l₁ : ℝ) + l₂)) * (r + lam₂ + lam₁)
          = lam₂ * (J (n + 1) - ((l₁ : ℝ) + l₂)) + lam₁ * (J (n - 1) - ((l₁ : ℝ) + l₂)) := by
      intro n h1 h2
      have e : J n * (r + lam₂ + lam₁) = ((l₁ : ℝ) + l₂) * r + J (n + 1) * lam₂ + J (n - 1) * lam₁ := by
        calc J n * (r + lam₂ + lam₁)
            = (((l₁ : ℝ) + l₂) * (r / (r + lam₂ + lam₁))
              + J (n + 1) * (lam₂ / (r + lam₂ + lam₁))
              + J (n - 1) * (lam₁ / (r + lam₂ + lam₁))) * (r + lam₂ + lam₁) := by rw [← h n h1 h2]
          _ = _ := by field_simp
      linear_combination e
    generalize hc : ((l₁ : ℝ) + l₂) = c at hK
    set K : ℤ → ℝ := fun n => J n - c with hKdef
    have hK' : ∀ n : ℤ, -(l₁ : ℤ) < n → n < (l₂ : ℤ) →
        K n * (r + lam₂ + lam₁) = lam₂ * K (n + 1) + lam₁ * K (n - 1) := hK
    set p : ℤ := -(l₁ : ℤ) with hp
    have hap : a ^ p ≠ 0 := zpow_ne_zero _ ha0.ne'
    have hbp : b ^ p ≠ 0 := zpow_ne_zero _ hb0.ne'
    have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
    set k₁ : ℝ := (K p * b - K (p + 1)) / (a ^ p * (b - a)) with hk₁
    set k₂ : ℝ := (K (p + 1) - a * K p) / (b ^ p * (b - a)) with hk₂
    have hQ0 : K p = k₁ * a ^ p + k₂ * b ^ p := by
      rw [hk₁, hk₂]; field_simp; ring
    have hQ1 : K (p + 1) = k₁ * a ^ (p + 1) + k₂ * b ^ (p + 1) := by
      rw [hk₁, hk₂, zpow_add_one₀ ha0.ne', zpow_add_one₀ hb0.ne']; field_simp; ring
    have step : ∀ n : ℤ, -(l₁ : ℤ) < n → n < (l₂ : ℤ) →
        K (n - 1) = k₁ * a ^ (n - 1) + k₂ * b ^ (n - 1) →
        K n = k₁ * a ^ n + k₂ * b ^ n →
        K (n + 1) = k₁ * a ^ (n + 1) + k₂ * b ^ (n + 1) := by
      intro n h1 h2 Qm Qn
      have := hK' n h1 h2
      have : lam₂ * K (n + 1) = lam₂ * (k₁ * a ^ (n + 1) + k₂ * b ^ (n + 1)) := by
        linear_combination (-1) * this + (r + lam₂ + lam₁) * Qn - lam₁ * Qm + k₁ * ra n + k₂ * rb n
      exact mul_left_cancel₀ hlam₂.ne' this
    have hP : ∀ m : ℕ, m + 1 ≤ l₁ + l₂ →
        (K (p + m) = k₁ * a ^ (p + m) + k₂ * b ^ (p + m)) ∧
        (K (p + m + 1) = k₁ * a ^ (p + m + 1) + k₂ * b ^ (p + m + 1)) := by
      intro m
      induction m with
      | zero => intro _; simpa using ⟨hQ0, hQ1⟩
      | succ m ih =>
        intro hm
        obtain ⟨i1, i2⟩ := ih (by omega)
        refine ⟨by push_cast; rw [← add_assoc]; exact i2, ?_⟩
        have := step (p + m + 1) (by omega) (by omega) (by rw [show p + (m : ℤ) + 1 - 1 = p + m by ring]; exact i1) i2
        push_cast
        rw [← add_assoc]
        exact this
    refine ⟨k₁, k₂, ?_⟩
    intro n hn1 hn2
    have hKn : K n = k₁ * a ^ n + k₂ * b ^ n := by
      obtain ⟨m, hm⟩ : ∃ m : ℕ, n = p + m := ⟨(n - p).toNat, by omega⟩
      rw [hm]
      by_cases hmm : m + 1 ≤ l₁ + l₂
      · exact (hP m hmm).1
      · obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = m' + 1 := ⟨m - 1, by omega⟩
        have := (hP m' (by omega)).2
        push_cast
        rw [← add_assoc]
        exact this
    have : J n - c = k₁ * a ^ n + k₂ * b ^ n := hKn
    linarith
  · rintro ⟨k₁, k₂, hJ⟩ n h1 h2
    have e0 := hJ n h1.le h2.le
    have e1 := hJ (n + 1) (by omega) (by omega)
    have e2 := hJ (n - 1) (by omega) (by omega)
    rw [e0, e1, e2]
    have ra' := ra n
    have rb' := rb n
    have key : (((l₁ : ℝ) + l₂) + k₁ * a ^ n + k₂ * b ^ n) * (r + lam₂ + lam₁)
        = ((l₁ : ℝ) + l₂) * r + (((l₁ : ℝ) + l₂) + k₁ * a ^ (n + 1) + k₂ * b ^ (n + 1)) * lam₂
          + (((l₁ : ℝ) + l₂) + k₁ * a ^ (n - 1) + k₂ * b ^ (n - 1)) * lam₁ := by
      linear_combination k₁ * ra' + k₂ * rb'
    field_simp
    linarith [key]


lemma gen_sol_aux (lam₁ lam₂ r : ℝ) (l₁ l₂ : ℕ)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hr : 0 < r) (hl : 1 ≤ l₁ + l₂)
    (J : ℤ → ℝ) :
    (∀ n : ℤ, -(l₁ : ℤ) < n → n < (l₂ : ℤ) →
        J n = ((l₁ : ℝ) + l₂) * (r / (r + lam₂ + lam₁))
              + J (n + 1) * (lam₂ / (r + lam₂ + lam₁))
              + J (n - 1) * (lam₁ / (r + lam₂ + lam₁))) ↔
      ∃ k₁ k₂ : ℝ, ∀ n : ℤ, -(l₁ : ℤ) ≤ n → n ≤ (l₂ : ℤ) →
        J n = (l₁ : ℝ) + l₂ + k₁ * alphaMinus lam₁ lam₂ r ^ n + k₂ * alphaPlus lam₁ lam₂ r ^ n := by
  obtain ⟨ha0, ha1, hb1, hra, hrb⟩ := root_facts lam₁ lam₂ r hlam₁ hlam₂ hr
  exact gen_sol_core lam₁ lam₂ r l₁ l₂ hlam₁ hlam₂ hr hl _ _ ha0 (by linarith) (by linarith) hra hrb J

end LNH

theorem solution (lam₁ lam₂ r : ℝ) (l₁ l₂ : ℕ)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hr : 0 < r) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂)
    (J : ℤ → ℝ) :
    let a := alphaMinus lam₁ lam₂ r
    let b := alphaPlus lam₁ lam₂ r
    (∀ n : ℤ, -(l₁ : ℤ) < n → n < (l₂ : ℤ) →
        J n = ((l₁ : ℝ) + l₂) * (r / (r + lam₂ + lam₁))
              + J (n + 1) * (lam₂ / (r + lam₂ + lam₁))
              + J (n - 1) * (lam₁ / (r + lam₂ + lam₁))) ↔
      ∃ k₁ k₂ : ℝ, ∀ n : ℤ, -(l₁ : ℤ) ≤ n → n ≤ (l₂ : ℤ) →
        J n = (l₁ : ℝ) + l₂ + k₁ * a ^ n + k₂ * b ^ n := by
  intro a b
  exact LNH.gen_sol_aux lam₁ lam₂ r l₁ l₂ hlam₁ hlam₂ hr (by omega) J
