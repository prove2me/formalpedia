-- Prove2me | solution 1 for LiuVanRyzin.capacity_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:06:49.645532+00:00
-- url     : https://prove2.me/submissions/61978a25-3265-4b6b-9bab-b1c56461bdb4

import Mathlib
import Definitions.Def_LiuVanRyzin_PowerModel

namespace LiuVanRyzin

theorem aux_lvrcap_ratio_lt (p₁ p₂ a b : ℝ) (hp : p₂ < p₁) (ha : p₁ ≤ a) (hab : a < b) :
    (a - p₁) / (a - p₂) < (b - p₁) / (b - p₂) := by
  have hA : 0 < a - p₂ := by linarith
  have hB : 0 < b - p₂ := by linarith
  rw [div_lt_div_iff₀ hA hB]
  nlinarith

theorem aux_lvrcap_ratio_nonneg (p₁ p₂ a : ℝ) (hp : p₂ < p₁) (ha : p₁ ≤ a) :
    0 ≤ (a - p₁) / (a - p₂) := by
  have hA : 0 < a - p₂ := by linarith
  exact div_nonneg (by linarith) hA.le

theorem aux_lvrcap_ratio_lt_one (p₁ p₂ a : ℝ) (hp : p₂ < p₁) (ha : p₁ ≤ a) :
    (a - p₁) / (a - p₂) < 1 := by
  have hA : 0 < a - p₂ := by linarith
  rw [div_lt_one hA]
  linarith

theorem aux_lvrcap_one_sub (p₁ p₂ a : ℝ) (hp : p₂ < p₁) (ha : p₁ ≤ a) :
    (a - p₁) / (a - p₂) - 1 = -(p₁ - p₂) / (a - p₂) := by
  have hA : 0 < a - p₂ := by linarith
  field_simp
  ring

end LiuVanRyzin

open LiuVanRyzin

theorem solution (N Ubar p₁ p₂ γ : ℝ) (hN : 0 < N) (hU : 0 < Ubar)
    (hp : p₂ < p₁) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    StrictMonoOn (capacity N Ubar p₁ p₂ γ) (Set.Icc p₁ Ubar) ∧
      StrictMonoOn (fillRate p₁ p₂ γ) (Set.Icc p₁ Ubar) := by
  constructor
  · intro a ha b hb hab
    have ha1 := ha.1
    unfold capacity fillRate
    have hNU : 0 < N / Ubar := div_pos hN hU
    apply mul_lt_mul_of_pos_left _ hNU
    set s := (a - p₁) / (a - p₂) with hs
    set t := (b - p₁) / (b - p₂) with ht
    have hst : s < t := aux_lvrcap_ratio_lt p₁ p₂ a b hp ha1 hab
    have hs0 : 0 ≤ s := aux_lvrcap_ratio_nonneg p₁ p₂ a hp ha1
    have ht1 : t < 1 := aux_lvrcap_ratio_lt_one p₁ p₂ b hp (by linarith)
    have hs1 : s < 1 := lt_trans hst ht1
    have key := (Real.strictConcaveOn_rpow hγ0 hγ1).secant_strict_mono
      (a := 1) (x := s) (y := t) (by simp) (by simpa using hs0)
      (by simp only [Set.mem_Ici]; linarith) hs1.ne ht1.ne hst
    simp only [Real.one_rpow] at key
    rw [aux_lvrcap_one_sub p₁ p₂ a hp ha1, aux_lvrcap_one_sub p₁ p₂ b hp (by linarith)] at key
    have hA : 0 < a - p₂ := by linarith
    have hB : 0 < b - p₂ := by linarith
    have hd : 0 < p₁ - p₂ := by linarith
    have e1 : ∀ (X B : ℝ), 0 < B → X / (-(p₁ - p₂) / B) = -X * B / (p₁ - p₂) := by
      intro X B hB
      field_simp
    rw [e1 _ _ hA, e1 _ _ hB, div_lt_div_iff_of_pos_right hd] at key
    nlinarith [key]
  · intro a ha b hb hab
    unfold fillRate
    exact Real.rpow_lt_rpow (aux_lvrcap_ratio_nonneg p₁ p₂ a hp ha.1)
      (aux_lvrcap_ratio_lt p₁ p₂ a b hp ha.1 hab) hγ0
