-- Prove2me | solution 1 for LNChannels.Exact.theorem_1_i_cost
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:03:48.302677+00:00
-- url     : https://prove2.me/submissions/78360fa9-ab4d-44a7-8a5d-90ff549d85c3

import Mathlib
import Definitions.Def_LNChannels_Exact_IsUniCostFn

set_option autoImplicit false
open LNChannels.Exact

theorem solution (lam₂ r B : ℝ) (l₂ : ℕ)
    (hlam₂ : 0 < lam₂) (hr : 0 < r) (hl₂ : 1 ≤ l₂) :
    (∃ J : ℤ → ℝ, IsUniCostFn lam₂ r B l₂ J) ∧
    ∀ J : ℤ → ℝ, IsUniCostFn lam₂ r B l₂ J →
      J 0 = (l₂ : ℝ) + B * (((r + lam₂) / lam₂) ^ l₂ - 1)⁻¹ := by
  generalize hρ : (r + lam₂) / lam₂ = ρ
  have hρ1 : 1 < ρ := by
    rw [← hρ, lt_div_iff₀ hlam₂]; linarith
  have hρpos : 0 < ρ := by linarith
  have hpow : 1 < ρ ^ l₂ := one_lt_pow₀ hρ1 (by omega)
  have hS : 0 < r + lam₂ := by linarith
  have hρl : ρ * lam₂ = r + lam₂ := by rw [← hρ]; field_simp
  constructor
  · refine ⟨fun n => (l₂ : ℝ) + (B * (ρ ^ l₂ - 1)⁻¹) * ρ ^ n, ?_, ?_⟩
    · intro n _ _
      simp only
      rw [zpow_add_one₀ hρpos.ne']
      field_simp
      linear_combination (-(B * ρ ^ n * (ρ ^ l₂ - 1)⁻¹)) * hρl
    · have h1 : ρ ^ l₂ - 1 ≠ 0 := by linarith
      simp only [zpow_natCast, zpow_zero, mul_one]
      field_simp
      ring
  · intro J ⟨hrec, hbd⟩
    have hind : ∀ k : ℕ, k ≤ l₂ → J k = (l₂ : ℝ) + (J 0 - l₂) * ρ ^ k := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have h := hrec k (by positivity) (by omega)
        have ih' := ih (by omega)
        push_cast at h ⊢
        rw [ih'] at h
        have h' : ((l₂ : ℝ) + (J 0 - l₂) * ρ ^ k) * (r + lam₂)
            = (l₂ : ℝ) * r + J (k + 1) * lam₂ := by
          field_simp at h
          linarith
        have : J (k + 1) * lam₂ = ((l₂ : ℝ) + (J 0 - l₂) * ρ ^ (k + 1)) * lam₂ := by
          rw [pow_succ]
          have : (J 0 - l₂) * (ρ ^ k * ρ) * lam₂ = (J 0 - l₂) * ρ ^ k * (ρ * lam₂) := by ring
          rw [add_mul, this, hρl]
          linarith
        exact mul_right_cancel₀ hlam₂.ne' this
    have h1 := hind l₂ le_rfl
    have h1 : ρ ^ l₂ - 1 ≠ 0 := by linarith
    have h2 := hind l₂ le_rfl
    rw [hbd] at h2
    field_simp
    have : (J 0 - l₂) * (ρ ^ l₂ - 1) = B := by linarith
    have hh : J 0 - l₂ = B / (ρ ^ l₂ - 1) := by field_simp; linarith
    rw [div_eq_mul_inv] at hh
    linarith
