-- Prove2me | solution 1 for LNChannels.Exact.theorem_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T17:58:20.951983+00:00
-- url     : https://prove2.me/submissions/611d4a3e-b9e1-47c1-b19a-ddcda4964f2a

import Mathlib
import Definitions.Def_LNChannels_Exact_alphaPlus
import Definitions.Def_LNChannels_Exact_alphaMinus
import Definitions.Def_LNChannels_Exact_IsBiCostFn

set_option autoImplicit false

namespace LNChBi74

/-- Discrete maximum principle for the homogeneous first-step equation. -/
lemma maxp (c₁ c₂ : ℝ) (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂) (h12 : c₁ + c₂ < 1) (l₁ l₂ : ℕ)
    (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) (K : ℤ → ℝ)
    (hrec : ∀ n : ℤ, -(l₁ : ℤ) < n → n < (l₂ : ℤ) → K n = K (n + 1) * c₂ + K (n - 1) * c₁)
    (hA : K (-(l₁ : ℤ)) = K 0) (hB : K (l₂ : ℤ) = K 0) :
    ∀ n : ℤ, -(l₁ : ℤ) ≤ n → n ≤ (l₂ : ℤ) → K n ≤ 0 := by
  obtain ⟨m, hm, hmax⟩ := (Finset.Icc (-(l₁ : ℤ)) (l₂ : ℤ)).exists_max_image K
    ⟨0, by rw [Finset.mem_Icc]; omega⟩
  rw [Finset.mem_Icc] at hm
  have hint : ∃ m' : ℤ, -(l₁ : ℤ) < m' ∧ m' < (l₂ : ℤ) ∧ K m' = K m := by
    by_cases hi : -(l₁ : ℤ) < m ∧ m < (l₂ : ℤ)
    · exact ⟨m, hi.1, hi.2, rfl⟩
    · refine ⟨0, by omega, by omega, ?_⟩
      rcases (show m = -(l₁ : ℤ) ∨ m = (l₂ : ℤ) by omega) with h | h
      · rw [h, hA]
      · rw [h, hB]
  obtain ⟨m', h1', h2', hK⟩ := hint
  have up : K (m' + 1) ≤ K m := hmax _ (by rw [Finset.mem_Icc]; omega)
  have dn : K (m' - 1) ≤ K m := hmax _ (by rw [Finset.mem_Icc]; omega)
  have hr := hrec m' h1' h2'
  have hMle : K m ≤ 0 := by nlinarith [mul_nonneg (sub_nonneg.2 up) h2, mul_nonneg (sub_nonneg.2 dn) h1]
  intro n hn1 hn2
  exact (hmax n (by rw [Finset.mem_Icc]; omega)).trans hMle

lemma zero_of_hom (c₁ c₂ : ℝ) (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂) (h12 : c₁ + c₂ < 1) (l₁ l₂ : ℕ)
    (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) (K : ℤ → ℝ)
    (hrec : ∀ n : ℤ, -(l₁ : ℤ) < n → n < (l₂ : ℤ) → K n = K (n + 1) * c₂ + K (n - 1) * c₁)
    (hA : K (-(l₁ : ℤ)) = K 0) (hB : K (l₂ : ℤ) = K 0) :
    ∀ n : ℤ, -(l₁ : ℤ) ≤ n → n ≤ (l₂ : ℤ) → K n = 0 := by
  intro n hn1 hn2
  have u := maxp c₁ c₂ h1 h2 h12 l₁ l₂ hl₁ hl₂ K hrec hA hB n hn1 hn2
  have v := maxp c₁ c₂ h1 h2 h12 l₁ l₂ hl₁ hl₂ (fun k => -K k)
    (fun k hk1 hk2 => by have := hrec k hk1 hk2; linear_combination -this)
    (by rw [hA]) (by rw [hB]) n hn1 hn2
  linarith

lemma root_rec (lam₁ lam₂ r x : ℝ) (hs : r + lam₂ + lam₁ ≠ 0) (hx : x ≠ 0)
    (h : lam₂ * x ^ 2 - (r + lam₂ + lam₁) * x + lam₁ = 0) (n : ℤ) :
    x ^ n = x ^ (n + 1) * (lam₂ / (r + lam₂ + lam₁)) + x ^ (n - 1) * (lam₁ / (r + lam₂ + lam₁)) := by
  rw [zpow_add_one₀ hx, zpow_sub_one₀ hx]
  field_simp
  linear_combination (-1 : ℝ) * h

end LNChBi74

open LNChBi74 in
open LNChannels.Exact in
theorem solution (lam₁ lam₂ r B : ℝ) (l₁ l₂ : ℕ)
    (hlam₁ : 0 < lam₁) (hlam : lam₁ ≤ lam₂) (hr : 0 < r) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) :
    let a := alphaMinus lam₁ lam₂ r
    let b := alphaPlus lam₁ lam₂ r
    (∃ J : ℤ → ℝ, IsBiCostFn lam₁ lam₂ r B l₁ l₂ J) ∧
    ∀ J : ℤ → ℝ, IsBiCostFn lam₁ lam₂ r B l₁ l₂ J →
      J 0 = (l₁ : ℝ) + l₂ - B *
        ((a ^ l₁ * (1 - b ^ (l₁ + l₂)) - b ^ l₁ * (1 - a ^ (l₁ + l₂))) /
          (a ^ l₁ * (1 - b ^ (l₁ + l₂)) - b ^ l₁ * (1 - a ^ (l₁ + l₂))
            + b ^ (l₁ + l₂) - a ^ (l₁ + l₂))) := by
  intro a b
  have hlam₂ : 0 < lam₂ := lt_of_lt_of_le hlam₁ hlam
  set s := r + lam₂ + lam₁ with hs_def
  have hs : 0 < s := by positivity
  set d := (lam₂ - lam₁) ^ 2 + r ^ 2 + 2 * r * (lam₂ + lam₁) with hd_def
  have hd : 0 < d := by positivity
  have hsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd.le
  have hsqpos : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hsd : s ^ 2 - d = 4 * lam₁ * lam₂ := by rw [hs_def, hd_def]; ring
  have ha_def : a = (s - Real.sqrt d) / (2 * lam₂) := by
    show alphaMinus lam₁ lam₂ r = _
    unfold alphaMinus; rw [hs_def, hd_def]; ring_nf
  have hb_def : b = (s + Real.sqrt d) / (2 * lam₂) := by
    show alphaPlus lam₁ lam₂ r = _
    unfold alphaPlus; rw [hs_def, hd_def]; ring_nf
  have hsgt : Real.sqrt d < s := by nlinarith
  have ha0 : 0 < a := by rw [ha_def]; apply div_pos <;> linarith
  have hb0 : 0 < b := by rw [hb_def]; apply div_pos <;> linarith
  have hab : a < b := by
    rw [ha_def, hb_def]; apply div_lt_div_of_pos_right _ (by linarith); linarith
  have hra : lam₂ * a ^ 2 - s * a + lam₁ = 0 := by
    rw [ha_def]; field_simp; nlinarith [hsq, hsd]
  have hrb : lam₂ * b ^ 2 - s * b + lam₁ = 0 := by
    rw [hb_def]; field_simp; nlinarith [hsq, hsd]
  have hc₁ : 0 ≤ lam₁ / s := by positivity
  have hc₂ : 0 ≤ lam₂ / s := by positivity
  have hc12 : lam₁ / s + lam₂ / s < 1 := by
    rw [← add_div, div_lt_one hs]; linarith
  set L : ℕ := l₁ + l₂ with hL
  set N := a ^ l₁ * (1 - b ^ L) - b ^ l₁ * (1 - a ^ L) with hN
  set E := a ^ L - b ^ L with hE
  -- homogeneous solution
  let K : ℤ → ℝ := fun n => (1 - b ^ L) * a ^ l₁ * a ^ n - (1 - a ^ L) * b ^ l₁ * b ^ n
  have hKrec : ∀ n : ℤ, K n = K (n + 1) * (lam₂ / s) + K (n - 1) * (lam₁ / s) := by
    intro n
    have h1 := root_rec lam₁ lam₂ r a hs.ne' ha0.ne' hra n
    have h2 := root_rec lam₁ lam₂ r b hs.ne' hb0.ne' hrb n
    simp only [K]
    rw [h1, h2]; ring
  have hKA : K (-(l₁ : ℤ)) = E := by
    simp only [K]
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast,
      mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha0.ne'),
      mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hb0.ne')]
    rw [hE]; ring
  have hK0 : K 0 = N := by simp only [K]; rw [zpow_zero, zpow_zero, hN]; ring
  have hKB : K (l₂ : ℤ) = E := by
    simp only [K]
    rw [zpow_natCast, zpow_natCast, hE, hL, pow_add, pow_add]; ring
  have hD : E - N ≠ 0 := by
    intro h0
    have hz := zero_of_hom (lam₁ / s) (lam₂ / s) hc₁ hc₂ hc12 l₁ l₂ hl₁ hl₂ K
      (fun n _ _ => hKrec n) (by rw [hKA, hK0]; linarith) (by rw [hKB, hK0]; linarith)
      (-(l₁ : ℤ)) le_rfl (by omega)
    rw [hKA, hE] at hz
    have hLpos : L ≠ 0 := by omega
    have := pow_lt_pow_left₀ hab ha0.le hLpos
    linarith
  set t := B / (E - N) with ht
  let Js : ℤ → ℝ := fun n => ((l₁ : ℝ) + l₂) + t * K n
  have hJs : LNChannels.Exact.IsBiCostFn lam₁ lam₂ r B l₁ l₂ Js := by
    refine ⟨?_, ?_, ?_⟩
    · intro n _ _
      simp only [Js]
      rw [← hs_def, hKrec n]
      field_simp
      ring
    · simp only [Js]; rw [hKA, hK0]
      have : t * (E - N) = B := by rw [ht]; field_simp
      linarith
    · simp only [Js]; rw [hKB, hK0]
      have : t * (E - N) = B := by rw [ht]; field_simp
      linarith
  have hJs0 : Js 0 = (l₁ : ℝ) + l₂ + t * N := by simp only [Js]; rw [hK0]
  refine ⟨⟨Js, hJs⟩, ?_⟩
  intro J hJ
  obtain ⟨hJr, hJA, hJB⟩ := hJ
  obtain ⟨hSr, hSA, hSB⟩ := hJs
  have hz := zero_of_hom (lam₁ / s) (lam₂ / s) hc₁ hc₂ hc12 l₁ l₂ hl₁ hl₂ (fun n => J n - Js n)
    (fun n h1 h2 => by
      have u := hJr n h1 h2
      have v := hSr n h1 h2
      rw [← hs_def] at u v
      linear_combination u - v)
    (by linear_combination hJA - hSA) (by linear_combination hJB - hSB) 0 (by omega) (by omega)
  have hJ0 : J 0 = (l₁ : ℝ) + l₂ + t * N := by rw [← hJs0]; linarith
  rw [hJ0, ht]
  have hden : N + b ^ L - a ^ L = -(E - N) := by rw [hE]; ring
  show (l₁ : ℝ) + l₂ + B / (E - N) * N = (l₁ : ℝ) + l₂ - B * (N / (N + b ^ L - a ^ L))
  rw [hden]
  field_simp
  ring
