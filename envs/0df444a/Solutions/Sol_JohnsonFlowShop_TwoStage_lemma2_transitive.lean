-- Prove2me | solution 1 for JohnsonFlowShop.TwoStage.lemma2_transitive
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:46:38.026973+00:00
-- url     : https://prove2.me/submissions/680c83ce-b168-4305-9795-0413063e3f69

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution (A₁ B₁ A₂ B₂ A₃ B₃ : ℝ)
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
