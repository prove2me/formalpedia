-- Prove2me | solution 1 for LiquidWelfareFPA.lambda2_equation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:58:06.333294+00:00
-- url     : https://prove2.me/submissions/4a249a50-73fc-441b-a051-e55625c1434d

import Mathlib
import Definitions.Def_LiquidWelfareFPA_lam2
import Definitions.Def_LiquidWelfareFPA_cfun

open LiquidWelfareFPA in
theorem solution (γ : ℝ) (hγ : 1 ≤ γ) :
    1 + 1 / lam2 γ = γ / (cfun (lam2 γ) * lam2 γ) ∧
      γ / (cfun (lam2 γ) * lam2 γ) = 1 + 1 / (γ * lambertW (-Real.exp (-2 / γ) / γ) + 1) := by
  have hγ0 : 0 < γ := by linarith
  obtain ⟨x, hxdef⟩ : ∃ x, x = -Real.exp (-2 / γ) / γ := ⟨_, rfl⟩
  have hxneg : x < 0 := by
    rw [hxdef, neg_div]
    have : 0 < Real.exp (-2 / γ) / γ := div_pos (Real.exp_pos _) hγ0
    linarith
  have hxlow : -Real.exp (-1) ≤ x := by
    have h2 : Real.exp (1 - 2 / γ) * Real.exp (-(1 - 2 / γ)) = 1 := by
      rw [← Real.exp_add]
      simp
    have h3 := Real.add_one_le_exp (-(1 - 2 / γ))
    have key : Real.exp (1 - 2 / γ) * (2 / γ) ≤ 1 := by
      have h4 := mul_le_mul_of_nonneg_left h3 (Real.exp_pos (1 - 2 / γ)).le
      have e3 : -(1 - 2 / γ) + 1 = 2 / γ := by ring
      rw [e3, h2] at h4
      exact h4
    have e : Real.exp (-2 / γ) = Real.exp (1 - 2 / γ) * Real.exp (-1) := by
      rw [← Real.exp_add]
      ring_nf
    have hk : Real.exp (1 - 2 / γ) * 2 ≤ γ := by
      have : Real.exp (1 - 2 / γ) * (2 / γ) * γ ≤ 1 * γ := mul_le_mul_of_nonneg_right key hγ0.le
      have e2 : Real.exp (1 - 2 / γ) * (2 / γ) * γ = Real.exp (1 - 2 / γ) * 2 := by
        field_simp
      linarith
    rw [hxdef, neg_div, neg_le_neg_iff, e, div_le_iff₀ hγ0]
    nlinarith [Real.exp_pos (-1), Real.exp_pos (1 - 2 / γ)]
  have hex : ∃ y : ℝ, -1 ≤ y ∧ y * Real.exp y = x := by
    have hcont : ContinuousOn (fun y : ℝ => y * Real.exp y) (Set.Icc (-1) 0) :=
      (continuous_id.mul Real.continuous_exp).continuousOn
    obtain ⟨y, hy, hyx⟩ := intermediate_value_Icc (by norm_num : (-1:ℝ) ≤ 0) hcont
      ⟨by simpa using hxlow, by simpa using hxneg.le⟩
    exact ⟨y, hy.1, hyx⟩
  have hspec : -1 ≤ lambertW x ∧ lambertW x * Real.exp (lambertW x) = x := by
    unfold lambertW
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  obtain ⟨W, hWdef⟩ : ∃ W, W = lambertW x := ⟨_, rfl⟩
  rw [← hWdef] at hspec
  obtain ⟨_, hWx⟩ := hspec
  have hWneg : W < 0 := by
    by_contra h
    push_neg at h
    have := mul_nonneg h (Real.exp_pos W).le
    linarith
  have hlog : Real.log (-W) + W = -2 / γ - Real.log γ := by
    have h1 : (-W) * Real.exp W = Real.exp (-2 / γ) / γ := by
      rw [hxdef] at hWx
      linear_combination -hWx
    have h2 := congrArg Real.log h1
    rw [Real.log_mul (neg_ne_zero.mpr hWneg.ne) (Real.exp_pos W).ne', Real.log_exp,
      Real.log_div (Real.exp_pos _).ne' hγ0.ne', Real.log_exp] at h2
    linarith
  have hlog1 : Real.log (1 - (γ * W + 1)) = -2 / γ - W := by
    rw [show 1 - (γ * W + 1) = γ * (-W) by ring, Real.log_mul hγ0.ne' (neg_ne_zero.mpr hWneg.ne)]
    linarith
  have hl0 : γ * W + 1 ≠ 0 := by
    intro h
    have hW' : W = -1 / γ := by
      rw [eq_div_iff hγ0.ne']
      linear_combination h
    rw [hW', hxdef] at hWx
    have e2 : (-1 / γ) * Real.exp (-1 / γ) = -(Real.exp (-1 / γ) / γ) := by ring
    have e3 : -Real.exp (-2 / γ) / γ = -(Real.exp (-2 / γ) / γ) := by ring
    rw [e2, e3, neg_inj, div_left_inj' hγ0.ne'] at hWx
    have h3 : (-1 : ℝ) / γ = -2 / γ := Real.exp_injective hWx
    rw [div_left_inj' hγ0.ne'] at h3
    norm_num at h3
  have hL : Real.log (1 - (γ * W + 1)) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by nlinarith [mul_pos hγ0 (neg_pos.mpr hWneg)])
      (by intro h; apply hl0; linarith)
  rw [hlog1] at hL
  have h1 : 1 + 1 / (γ * W + 1) = γ / (-1 / (-2 / γ - W) * (γ * W + 1)) := by
    field_simp <;> ring
  unfold lam2 cfun
  rw [← hxdef, ← hWdef, hlog1]
  exact ⟨h1, h1.symm⟩
