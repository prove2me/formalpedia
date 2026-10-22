-- Prove2me | solution 1 for NatureSLT.Margin.optimal_hyperplane_delta_margin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:00:21.510814+00:00
-- url     : https://prove2.me/submissions/ff9271f2-6b58-4dfa-b70e-f8b20bd2c7bf

import Mathlib
import Definitions.Def_NatureSLT_Margin_optimalHyperplane
import Definitions.Def_NatureSLT_Margin_marginVCDim

open NatureSLT.Margin
open scoped InnerProductSpace

theorem solution {n ℓ : ℕ} (x : Fin ℓ → EuclideanSpace ℝ (Fin n))
    (y : Fin ℓ → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) (hboth : (∃ i, y i = 1) ∧ ∃ j, y j = -1)
    (w₀ : EuclideanSpace ℝ (Fin n)) (b₀ : ℝ) (hopt : IsOptimalHyperplane x y w₀ b₀) :
    w₀ ≠ 0 ∧ ‖‖w₀‖⁻¹ • w₀‖ = 1 ∧
      ∀ i, MarginClassifies (‖w₀‖⁻¹ • w₀) (b₀ / ‖w₀‖) (1 / ‖w₀‖) (x i) (decide (y i = 1)) := by
  have hsep := hopt.1
  have hw : w₀ ≠ 0 := by
    rintro rfl
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hboth
    have h1 := hsep i
    have h2 := hsep j
    simp [hi, hj] at h1 h2
    linarith
  have hn : 0 < ‖w₀‖ := norm_pos_iff.mpr hw
  refine ⟨hw, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  · intro i
    have h := hsep i
    have key : ⟪‖w₀‖⁻¹ • w₀, x i⟫_ℝ - b₀ / ‖w₀‖ = (⟪w₀, x i⟫_ℝ - b₀) / ‖w₀‖ := by
      rw [real_inner_smul_left]; field_simp
    constructor
    · intro hyi
      have : y i = 1 := by simpa using hyi
      rw [key]
      rw [this, one_mul] at h
      exact div_le_div_of_nonneg_right h hn.le
    · intro hyi
      have : y i = -1 := by
        rcases hy i with h1 | h1
        · simp [h1] at hyi
        · exact h1
      rw [key]
      rw [this] at h
      rw [div_le_iff₀ hn]
      have : -(1 / ‖w₀‖) * ‖w₀‖ = -1 := by field_simp
      rw [this]; linarith
