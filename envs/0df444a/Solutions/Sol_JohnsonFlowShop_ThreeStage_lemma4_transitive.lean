-- Prove2me | solution 1 for JohnsonFlowShop.ThreeStage.lemma4_transitive
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:41:45.584105+00:00
-- url     : https://prove2.me/submissions/cb0fcd8c-5fdb-4cbd-85f4-d3924c6963ed

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem two_stage_transitive (A₁ B₁ A₂ B₂ A₃ B₃ : ℝ)
    (h₁₂ : min A₁ B₂ ≤ min A₂ B₁) (h₂₃ : min A₂ B₃ ≤ min A₃ B₂) :
    min A₁ B₃ ≤ min A₃ B₁ ∨ (min A₁ B₂ = min A₂ B₁ ∧ min A₂ B₃ = min A₃ B₂) := by
  by_cases h₁₃ : min A₁ B₃ ≤ min A₃ B₁
  · exact Or.inl h₁₃
  · right
    have h₂₁ : min A₂ B₁ ≤ min A₁ B₂ := by
      simp only [min_def] at *
      split_ifs at * <;> linarith
    have h₃₂ : min A₃ B₂ ≤ min A₂ B₃ := by
      simp only [min_def] at *
      split_ifs at * <;> linarith
    exact ⟨le_antisymm h₁₂ h₂₁, le_antisymm h₂₃ h₃₂⟩

theorem solution (A₁ B₁ C₁ A₂ B₂ C₂ A₃ B₃ C₃ : ℝ)
    (h₁₂ : min (A₁ + B₁) (C₂ + B₂) ≤ min (A₂ + B₂) (C₁ + B₁))
    (h₂₃ : min (A₂ + B₂) (C₃ + B₃) ≤ min (A₃ + B₃) (C₂ + B₂)) :
    min (A₁ + B₁) (C₃ + B₃) ≤ min (A₃ + B₃) (C₁ + B₁) ∨
      (min (A₁ + B₁) (C₂ + B₂) = min (A₂ + B₂) (C₁ + B₁) ∧
        min (A₂ + B₂) (C₃ + B₃) = min (A₃ + B₃) (C₂ + B₂))  := by
  exact two_stage_transitive (A₁+B₁) (C₁+B₁) (A₂+B₂) (C₂+B₂)
    (A₃+B₃) (C₃+B₃) h₁₂ h₂₃
