-- Prove2me | solution 1 for NumStochOpt.LogConcave.theorem_5_7_1_mixed_derivative_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T05:48:39.761915+00:00
-- url     : https://prove2.me/submissions/866ed4b3-4a2e-4d26-9f6b-987dd31a6abf

import Mathlib
import Definitions.Def_NumStochOpt_LogConcave_polyDistF

set_option autoImplicit false

namespace P2M_2fe705a5

open Finset

/-- Weighted pair inequality: for oppositely ordered nonpositive sequences,
`2 (∑ w a)(∑ w b) ≥ (∑ w)(∑ w a b)`. -/
lemma key {N : ℕ} (w a b : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, a i ≤ 0)
    (hb : ∀ i, b i ≤ 0) (hmono : Monotone a) (hanti : Antitone b) :
    0 ≤ 2 * ((∑ i, w i * a i) * (∑ i, w i * b i)) - (∑ i, w i) * (∑ i, w i * a i * b i) := by
  have hpt : ∀ i j, 0 ≤ w i * w j * (-(a i - a j) * (b i - b j) + a i * b j + a j * b i) := by
    intro i j
    apply mul_nonneg (mul_nonneg (hw i) (hw j))
    have h1 : 0 ≤ -(a i - a j) * (b i - b j) := by
      rcases le_total i j with h | h
      · have h1 := hmono h; have h2 := hanti h; nlinarith
      · have h1 := hmono h; have h2 := hanti h; nlinarith
    have h2 : 0 ≤ a i * b j := mul_nonneg_of_nonpos_of_nonpos (ha i) (hb j)
    have h3 : 0 ≤ a j * b i := mul_nonneg_of_nonpos_of_nonpos (ha j) (hb i)
    linarith
  have hsum : 0 ≤ ∑ i, ∑ j, w i * w j * (-(a i - a j) * (b i - b j) + a i * b j + a j * b i) :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => hpt i j
  have e1 : ∀ i j, w i * w j * (-(a i - a j) * (b i - b j) + a i * b j + a j * b i)
      = 2 * ((w i * a i) * (w j * b j)) + 2 * ((w j * a j) * (w i * b i))
        - (w i * a i * b i) * w j - w i * (w j * a j * b j) := by
    intro i j; ring
  have heq : ∑ i, ∑ j, w i * w j * (-(a i - a j) * (b i - b j) + a i * b j + a j * b i)
      = 2 * (2 * ((∑ i, w i * a i) * (∑ i, w i * b i))
        - (∑ i, w i) * (∑ i, w i * a i * b i)) := by
    simp only [e1, sum_sub_distrib, sum_add_distrib, ← mul_sum, ← sum_mul]
    ring
  linarith

end P2M_2fe705a5

open P2M_2fe705a5 in
open NumStochOpt.LogConcave in
theorem solution {N : ℕ} (hN : 0 < N)
    (c : Fin N → ℝ) (hc : ∀ i, 0 < c i)
    (α : Fin N → Fin 2 → ℝ) (hα : ∀ i j, α i j ≤ 0) (hα_sum : ∀ i, ∑ j, α i j < 0)
    (hα_mono : Monotone (fun i => α i 0)) (hα_anti : Antitone (fun i => α i 1))
    (z₁ z₂ : ℝ) (hz₁ : 0 < z₁) (hz₁' : z₁ < 1) (hz₂ : 0 < z₂) (hz₂' : z₂ < 1) :
    0 ≤ deriv (fun s => deriv (fun t => polyDistF c α ![s, t]) z₂) z₁ := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hF : ∀ s t, polyDistF c α ![s, t] = (∑ i, c i * (s ^ α i 0 * t ^ α i 1))⁻¹ := by
    intro s t; simp [polyDistF, Fin.prod_univ_two]
  have hSpos : ∀ s t, 0 < s → 0 < t → 0 < ∑ i, c i * (s ^ α i 0 * t ^ α i 1) := by
    intro s t hs ht
    exact Finset.sum_pos (fun i _ => by have := hc i; positivity) Finset.univ_nonempty
  -- inner derivative
  have hin : ∀ s, 0 < s → deriv (fun t => polyDistF c α ![s, t]) z₂
      = -(∑ i, c i * (s ^ α i 0 * (α i 1 * z₂ ^ (α i 1 - 1))))
          / (∑ i, c i * (s ^ α i 0 * z₂ ^ α i 1)) ^ 2 := by
    intro s hs
    have h1 : HasDerivAt (fun t => ∑ i, c i * (s ^ α i 0 * t ^ α i 1))
        (∑ i, c i * (s ^ α i 0 * (α i 1 * z₂ ^ (α i 1 - 1)))) z₂ := by
      apply HasDerivAt.fun_sum
      intro i _
      exact ((Real.hasDerivAt_rpow_const (Or.inl hz₂.ne')).const_mul (s ^ α i 0)).const_mul (c i)
    have h2 := h1.fun_inv (hSpos s z₂ hs hz₂).ne'
    rw [show (fun t => polyDistF c α ![s, t])
        = fun t => (∑ i, c i * (s ^ α i 0 * t ^ α i 1))⁻¹ from funext (hF s)]
    exact h2.deriv
  have hev : (fun s => deriv (fun t => polyDistF c α ![s, t]) z₂) =ᶠ[nhds z₁]
      (fun s => -(∑ i, c i * (s ^ α i 0 * (α i 1 * z₂ ^ (α i 1 - 1))))
          / (∑ i, c i * (s ^ α i 0 * z₂ ^ α i 1)) ^ 2) :=
    (lt_mem_nhds hz₁).mono fun s hs => hin s hs
  rw [hev.deriv_eq]
  have hnum : HasDerivAt (fun s => ∑ i, c i * (s ^ α i 0 * (α i 1 * z₂ ^ (α i 1 - 1))))
      (∑ i, c i * ((α i 0 * z₁ ^ (α i 0 - 1)) * (α i 1 * z₂ ^ (α i 1 - 1)))) z₁ := by
    apply HasDerivAt.fun_sum
    intro i _
    exact ((Real.hasDerivAt_rpow_const (Or.inl hz₁.ne')).mul_const _).const_mul (c i)
  have hden : HasDerivAt (fun s => ∑ i, c i * (s ^ α i 0 * z₂ ^ α i 1))
      (∑ i, c i * ((α i 0 * z₁ ^ (α i 0 - 1)) * z₂ ^ α i 1)) z₁ := by
    apply HasDerivAt.fun_sum
    intro i _
    exact ((Real.hasDerivAt_rpow_const (Or.inl hz₁.ne')).mul_const _).const_mul (c i)
  have hD := hSpos z₁ z₂ hz₁ hz₂
  have hg := hnum.fun_neg.fun_div (hden.fun_pow 2) (by positivity)
  rw [hg.deriv]
  -- reduce to the key inequality
  set w : Fin N → ℝ := fun i => c i * (z₁ ^ α i 0 * z₂ ^ α i 1) with hw_def
  have hwnn : ∀ i, 0 ≤ w i := fun i => by have := hc i; positivity
  have eW : ∑ i, c i * (z₁ ^ α i 0 * z₂ ^ α i 1) = ∑ i, w i := rfl
  have eB : ∑ i, c i * (z₁ ^ α i 0 * (α i 1 * z₂ ^ (α i 1 - 1)))
      = (∑ i, w i * α i 1) / z₂ := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.rpow_sub_one hz₂.ne']; simp only [hw_def]; field_simp
  have eA : ∑ i, c i * ((α i 0 * z₁ ^ (α i 0 - 1)) * z₂ ^ α i 1)
      = (∑ i, w i * α i 0) / z₁ := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.rpow_sub_one hz₁.ne']; simp only [hw_def]; field_simp
  have eC : ∑ i, c i * ((α i 0 * z₁ ^ (α i 0 - 1)) * (α i 1 * z₂ ^ (α i 1 - 1)))
      = (∑ i, w i * α i 0 * α i 1) / (z₁ * z₂) := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.rpow_sub_one hz₁.ne', Real.rpow_sub_one hz₂.ne']; simp only [hw_def]; field_simp
  rw [eW, eB, eA, eC]
  have hK := key w (fun i => α i 0) (fun i => α i 1) hwnn (fun i => hα i 0) (fun i => hα i 1)
    hα_mono hα_anti
  have hWpos : 0 < ∑ i, w i := by rw [← eW]; exact hD
  set W := ∑ i, w i
  set A := ∑ i, w i * α i 0
  set B := ∑ i, w i * α i 1
  set C := ∑ i, w i * α i 0 * α i 1
  have hfin : (-(C / (z₁ * z₂)) * W ^ 2 - -(B / z₂) * ((2 : ℕ) * W ^ (2 - 1) * (A / z₁)))
      / (W ^ 2) ^ 2 = (W * (2 * (A * B) - W * C)) / (z₁ * z₂) / (W ^ 2) ^ 2 := by
    congr 1; field_simp; push_cast; ring
  rw [hfin]
  have h0 : 0 ≤ W * (2 * (A * B) - W * C) := mul_nonneg hWpos.le hK
  exact div_nonneg (div_nonneg h0 (by positivity)) (by positivity)
