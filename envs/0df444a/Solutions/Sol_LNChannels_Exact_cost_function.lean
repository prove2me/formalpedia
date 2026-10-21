-- Prove2me | solution 1 for LNChannels.Exact.cost_function
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:00:07.922224+00:00
-- url     : https://prove2.me/submissions/67f0a5df-12bb-4aaa-a8b5-a1945ae1914a

import Mathlib
import Definitions.Def_LNChannels_Exact_alphaPlus
import Definitions.Def_LNChannels_Exact_alphaMinus
import Definitions.Def_LNChannels_Exact_IsBiCostFn

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
namespace LNH

lemma mp_le (l1 l2 r : ℝ) (h1 : 0 < l1) (h2 : 0 < l2) (hr : 0 < r) (K : ℤ → ℝ) (p q : ℤ)
    (hpq : p ≤ q)
    (hrec : ∀ n, p < n → n < q → K n * (r + l2 + l1) = l2 * K (n + 1) + l1 * K (n - 1))
    (M : ℝ) (hM : 0 ≤ M) (hp : K p ≤ M) (hq : K q ≤ M) :
    ∀ n, p ≤ n → n ≤ q → K n ≤ M := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨n0, hn0p, hn0q, hn0⟩ := hcon
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.Icc p q) K
    ⟨p, Finset.mem_Icc.2 ⟨le_rfl, hpq⟩⟩
  have hm' := Finset.mem_Icc.1 hm
  have hKm : M < K m := lt_of_lt_of_le hn0 (hmax n0 (Finset.mem_Icc.2 ⟨hn0p, hn0q⟩))
  have hmp : p < m := lt_of_le_of_ne hm'.1 (by rintro rfl; linarith)
  have hmq : m < q := lt_of_le_of_ne hm'.2 (by rintro rfl; linarith)
  have e := hrec m hmp hmq
  have u1 := hmax (m + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have u2 := hmax (m - 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  nlinarith [mul_le_mul_of_nonneg_left u1 h2.le, mul_le_mul_of_nonneg_left u2 h1.le,
    mul_pos (lt_of_le_of_lt hM hKm) hr]

lemma mp_two (l1 l2 r : ℝ) (h1 : 0 < l1) (h2 : 0 < l2) (hr : 0 < r) (L₁ L₂ : ℕ)
    (hL₁ : 1 ≤ L₁) (hL₂ : 1 ≤ L₂) (K : ℤ → ℝ)
    (hrec : ∀ n : ℤ, -(L₁ : ℤ) < n → n < (L₂ : ℤ) →
      K n * (r + l2 + l1) = l2 * K (n + 1) + l1 * K (n - 1))
    (e1 : K (-(L₁ : ℤ)) = K 0) (e2 : K (L₂ : ℤ) = K 0) :
    ∀ n : ℤ, -(L₁ : ℤ) ≤ n → n ≤ (L₂ : ℤ) → K n = 0 := by
  have C : ∀ F : ℤ → ℝ, (∀ n : ℤ, -(L₁ : ℤ) < n → n < (L₂ : ℤ) →
      F n * (r + l2 + l1) = l2 * F (n + 1) + l1 * F (n - 1)) →
      F (-(L₁ : ℤ)) = F 0 → F (L₂ : ℤ) = F 0 → 0 ≤ F 0 →
      F 0 = 0 ∧ ∀ n : ℤ, -(L₁ : ℤ) ≤ n → n ≤ (L₂ : ℤ) → F n ≤ 0 := by
    intro F hF f1 f2 f0
    have hb : ∀ n : ℤ, -(L₁ : ℤ) ≤ n → n ≤ (L₂ : ℤ) → F n ≤ F 0 := by
      intro n hn1 hn2
      by_cases hn : n ≤ 0
      · exact mp_le l1 l2 r h1 h2 hr F (-(L₁ : ℤ)) 0 (by omega)
          (fun m hm1 hm2 => hF m hm1 (by omega)) (F 0) f0 (le_of_eq f1) le_rfl n hn1 hn
      · exact mp_le l1 l2 r h1 h2 hr F 0 (L₂ : ℤ) (by omega)
          (fun m hm1 hm2 => hF m (by omega) hm2) (F 0) f0 le_rfl (le_of_eq f2) n (by omega) hn2
    have h0 : F 0 = 0 := by
      by_contra hne
      have hpos : 0 < F 0 := lt_of_le_of_ne f0 (Ne.symm hne)
      have e := hF 0 (by omega) (by omega)
      have u1 := hb 1 (by omega) (by omega)
      have u2 := hb (-1) (by omega) (by omega)
      norm_num at e
      nlinarith [mul_le_mul_of_nonneg_left u1 h2.le, mul_le_mul_of_nonneg_left u2 h1.le,
        mul_pos hpos hr]
    refine ⟨h0, fun n hn1 hn2 => ?_⟩
    have := hb n hn1 hn2
    linarith
  intro n hn1 hn2
  rcases le_or_gt 0 (K 0) with h0 | h0
  · obtain ⟨hz, hle⟩ := C K hrec e1 e2 h0
    obtain ⟨_, hle'⟩ := C (fun m => -K m)
      (fun m a b => by have := hrec m a b; linarith) (by simp [e1]) (by simp [e2]) (by simp [hz])
    have := hle n hn1 hn2
    have := hle' n hn1 hn2
    linarith
  · obtain ⟨hz, _⟩ := C (fun m => -K m)
      (fun m a b => by have := hrec m a b; linarith) (by simp [e1]) (by simp [e2]) (by simp; linarith)
    linarith

def BI (lam₁ lam₂ r B : ℝ) (l₁ l₂ : ℕ) (J : ℤ → ℝ) : Prop :=
  (∀ n : ℤ, -(l₁ : ℤ) < n → n < (l₂ : ℤ) →
      J n = ((l₁ : ℝ) + l₂) * (r / (r + lam₂ + lam₁))
            + J (n + 1) * (lam₂ / (r + lam₂ + lam₁))
            + J (n - 1) * (lam₁ / (r + lam₂ + lam₁))) ∧
  J (-(l₁ : ℤ)) = J 0 + B ∧ J (l₂ : ℤ) = J 0 + B

lemma cost_core (lam₁ lam₂ r B : ℝ) (l₁ l₂ : ℕ) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hr : 0 < r)
    (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hb1 : 1 < b)
    (hra : lam₂ * a ^ 2 - (lam₁ + lam₂ + r) * a + lam₁ = 0)
    (hrb : lam₂ * b ^ 2 - (lam₁ + lam₂ + r) * b + lam₁ = 0) :
    (∃ J : ℤ → ℝ, BI lam₁ lam₂ r B l₁ l₂ J) ∧
    ∀ J : ℤ → ℝ, BI lam₁ lam₂ r B l₁ l₂ J →
      ∀ n : ℤ, -(l₁ : ℤ) ≤ n → n ≤ (l₂ : ℤ) →
        J n = (l₁ : ℝ) + l₂ - B *
          (((a ^ (l₁ + l₂) - 1) * b ^ ((l₁ : ℤ) + n) - (b ^ (l₁ + l₂) - 1) * a ^ ((l₁ : ℤ) + n)) /
            (a ^ l₁ - b ^ l₁ + (b ^ l₁ - 1) * a ^ (l₁ + l₂) - (a ^ l₁ - 1) * b ^ (l₁ + l₂))) := by
  have hb0 : 0 < b := by linarith
  have hab : a < b := by linarith
  have hS : 0 < r + lam₂ + lam₁ := by positivity
  have ra := zpow_rec lam₁ lam₂ r a ha0 hra
  have rb := zpow_rec lam₁ lam₂ r b hb0 hrb
  obtain ⟨x, hx⟩ : ∃ x, a ^ l₁ = x := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, b ^ l₁ = y := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, a ^ l₂ = X := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, b ^ l₂ = Y := ⟨_, rfl⟩
  have hx0 : 0 < x := hx ▸ pow_pos ha0 _
  have hx1 : x < 1 := hx ▸ pow_lt_one₀ ha0.le ha1 (by omega)
  have hy1 : 1 < y := hy ▸ one_lt_pow₀ hb1 (by omega)
  have hX0 : 0 < X := hX ▸ pow_pos ha0 _
  have hX1 : X < 1 := hX ▸ pow_lt_one₀ ha0.le ha1 (by omega)
  have hY1 : 1 < Y := hY ▸ one_lt_pow₀ hb1 (by omega)
  have hy0 : 0 < y := by linarith
  have hx' : x ≠ 0 := hx0.ne'
  have hy' : y ≠ 0 := hy0.ne'
  have hnegA : a ^ (-(l₁ : ℤ)) = x⁻¹ := by rw [zpow_neg, zpow_natCast, hx]
  have hnegB : b ^ (-(l₁ : ℤ)) = y⁻¹ := by rw [zpow_neg, zpow_natCast, hy]
  have hposA : a ^ (l₂ : ℤ) = X := by rw [zpow_natCast, hX]
  have hposB : b ^ (l₂ : ℤ) = Y := by rw [zpow_natCast, hY]
  have hΔ : y * (1 - x) * (Y - 1) - x * (1 - y) * (X - 1) ≠ 0 := by
    intro h0
    have hrecW : ∀ n : ℤ, -(l₁ : ℤ) < n → n < (l₂ : ℤ) →
        (x * (1 - y) * a ^ n + (-(y * (1 - x))) * b ^ n) * (r + lam₂ + lam₁)
          = lam₂ * (x * (1 - y) * a ^ (n + 1) + (-(y * (1 - x))) * b ^ (n + 1))
            + lam₁ * (x * (1 - y) * a ^ (n - 1) + (-(y * (1 - x))) * b ^ (n - 1)) := by
      intro n _ _
      linear_combination (x * (1 - y)) * ra n + (-(y * (1 - x))) * rb n
    have hW1 : x * (1 - y) * a ^ (-(l₁ : ℤ)) + (-(y * (1 - x))) * b ^ (-(l₁ : ℤ))
        = x * (1 - y) * a ^ (0 : ℤ) + (-(y * (1 - x))) * b ^ (0 : ℤ) := by
      rw [hnegA, hnegB, zpow_zero, zpow_zero]
      field_simp
      ring
    have hW2 : x * (1 - y) * a ^ (l₂ : ℤ) + (-(y * (1 - x))) * b ^ (l₂ : ℤ)
        = x * (1 - y) * a ^ (0 : ℤ) + (-(y * (1 - x))) * b ^ (0 : ℤ) := by
      rw [hposA, hposB, zpow_zero, zpow_zero]
      linear_combination (-1) * h0
    have := mp_two lam₁ lam₂ r hlam₁ hlam₂ hr l₁ l₂ hl₁ hl₂
      (fun n => x * (1 - y) * a ^ n + (-(y * (1 - x))) * b ^ n) hrecW hW1 hW2 0
      (by omega) (by omega)
    simp only [zpow_zero] at this
    nlinarith
  obtain ⟨Δ, hΔd⟩ : ∃ Δ, Δ = y * (1 - x) * (Y - 1) - x * (1 - y) * (X - 1) := ⟨_, rfl⟩
  rw [← hΔd] at hΔ
  have hden : a ^ l₁ - b ^ l₁ + (b ^ l₁ - 1) * a ^ (l₁ + l₂) - (a ^ l₁ - 1) * b ^ (l₁ + l₂) = Δ := by
    rw [pow_add, pow_add, hx, hy, hX, hY, hΔd]; ring
  have hnum : ∀ n : ℤ, ((a ^ (l₁ + l₂) - 1) * b ^ ((l₁ : ℤ) + n)
      - (b ^ (l₁ + l₂) - 1) * a ^ ((l₁ : ℤ) + n))
      = (x * X - 1) * (y * b ^ n) - (y * Y - 1) * (x * a ^ n) := by
    intro n
    rw [zpow_add₀ ha0.ne', zpow_add₀ hb0.ne', zpow_natCast, zpow_natCast, pow_add, pow_add,
      hx, hy, hX, hY]
  constructor
  · obtain ⟨k₁, hk₁⟩ : ∃ k₁ : ℝ, k₁ = B * x * (y * Y - 1) / Δ := ⟨_, rfl⟩
    obtain ⟨k₂, hk₂⟩ : ∃ k₂ : ℝ, k₂ = B * y * (1 - x * X) / Δ := ⟨_, rfl⟩
    have hk1 : k₁ * Δ = B * x * (y * Y - 1) := by rw [hk₁]; field_simp
    have hk2 : k₂ * Δ = B * y * (1 - x * X) := by rw [hk₂]; field_simp
    have E1 : k₁ * y * (1 - x) + k₂ * x * (1 - y) = B * x * y := by
      apply mul_right_cancel₀ hΔ
      rw [hΔd] at hk1 hk2 ⊢
      linear_combination (y * (1 - x)) * hk1 + (x * (1 - y)) * hk2
    have E2 : k₁ * (X - 1) + k₂ * (Y - 1) = B := by
      apply mul_right_cancel₀ hΔ
      rw [hΔd] at hk1 hk2 ⊢
      linear_combination (X - 1) * hk1 + (Y - 1) * hk2
    refine ⟨fun n => (l₁ : ℝ) + l₂ + k₁ * a ^ n + k₂ * b ^ n, ?_⟩
    unfold BI
    refine ⟨(gen_sol_core lam₁ lam₂ r l₁ l₂ hlam₁ hlam₂ hr (by omega) a b ha0 hb0 hab hra hrb
      (fun n => (l₁ : ℝ) + l₂ + k₁ * a ^ n + k₂ * b ^ n)).2 ⟨k₁, k₂, fun n _ _ => rfl⟩, ?_, ?_⟩
    · beta_reduce
      rw [hnegA, hnegB, zpow_zero, zpow_zero]
      have hxi : x * x⁻¹ = 1 := mul_inv_cancel₀ hx'
      have hyi : y * y⁻¹ = 1 := mul_inv_cancel₀ hy'
      have : k₁ * x⁻¹ + k₂ * y⁻¹ = k₁ + k₂ + B := by
        apply mul_left_cancel₀ (mul_ne_zero hx' hy')
        linear_combination E1 + (k₁ * y) * hxi + (k₂ * x) * hyi
      linarith
    · beta_reduce
      rw [hposA, hposB, zpow_zero, zpow_zero]
      linarith
  · intro J hJ n hn1 hn2
    obtain ⟨hrec, hb1', hb2'⟩ := hJ
    obtain ⟨k₁, k₂, hJ⟩ := (gen_sol_core lam₁ lam₂ r l₁ l₂ hlam₁ hlam₂ hr (by omega) a b ha0 hb0 hab hra hrb
      J).1 hrec
    have e1 := hb1'
    rw [hJ (-(l₁ : ℤ)) le_rfl (by omega), hJ 0 (by omega) (by omega), hnegA, hnegB, zpow_zero,
      zpow_zero] at e1
    have e2 := hb2'
    rw [hJ (l₂ : ℤ) (by omega) le_rfl, hJ 0 (by omega) (by omega), hposA, hposB, zpow_zero,
      zpow_zero] at e2
    have hxi : x * x⁻¹ = 1 := mul_inv_cancel₀ hx'
    have hyi : y * y⁻¹ = 1 := mul_inv_cancel₀ hy'
    have E1 : k₁ * y * (1 - x) + k₂ * x * (1 - y) = B * x * y := by
      linear_combination (x * y) * e1 - (k₁ * y) * hxi - (k₂ * x) * hyi
    have E2 : k₁ * (X - 1) + k₂ * (Y - 1) = B := by linarith
    have hk1 : k₁ * Δ = B * x * (y * Y - 1) := by
      rw [hΔd]; linear_combination (Y - 1) * E1 - x * (1 - y) * E2
    have hk2 : k₂ * Δ = B * y * (1 - x * X) := by
      rw [hΔd]; linear_combination y * (1 - x) * E2 - (X - 1) * E1
    have hk1' : k₁ = B * x * (y * Y - 1) / Δ := by rw [eq_div_iff hΔ]; exact hk1
    have hk2' : k₂ = B * y * (1 - x * X) / Δ := by rw [eq_div_iff hΔ]; exact hk2
    rw [hJ n hn1 hn2, hnum n, hden, hk1', hk2']
    field_simp
    ring

end LNH

theorem solution (lam₁ lam₂ r B : ℝ) (l₁ l₂ : ℕ)
    (hlam₁ : 0 < lam₁) (hlam : lam₁ ≤ lam₂) (hr : 0 < r) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) :
    let a := alphaMinus lam₁ lam₂ r
    let b := alphaPlus lam₁ lam₂ r
    (∃ J : ℤ → ℝ, IsBiCostFn lam₁ lam₂ r B l₁ l₂ J) ∧
    ∀ J : ℤ → ℝ, IsBiCostFn lam₁ lam₂ r B l₁ l₂ J →
      ∀ n : ℤ, -(l₁ : ℤ) ≤ n → n ≤ (l₂ : ℤ) →
        J n = (l₁ : ℝ) + l₂ - B *
          (((a ^ (l₁ + l₂) - 1) * b ^ ((l₁ : ℤ) + n) - (b ^ (l₁ + l₂) - 1) * a ^ ((l₁ : ℤ) + n)) /
            (a ^ l₁ - b ^ l₁ + (b ^ l₁ - 1) * a ^ (l₁ + l₂) - (a ^ l₁ - 1) * b ^ (l₁ + l₂))) := by
  intro a b
  obtain ⟨ha0, ha1, hb1, hra, hrb⟩ := LNH.root_facts lam₁ lam₂ r hlam₁ (by linarith) hr
  exact LNH.cost_core lam₁ lam₂ r B l₁ l₂ hl₁ hl₂ hlam₁ (by linarith) hr _ _ ha0 ha1 hb1 hra hrb
