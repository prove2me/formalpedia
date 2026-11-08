-- Prove2me | solution 1 for LowDepthPRF.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:12:25.084041+00:00
-- url     : https://prove2.me/submissions/1bbe02d1-182b-47ae-8c9a-22faaa7e4f01

import Mathlib
import Definitions.Def_LowDepthPRF_Game

open LowDepthPRF in
theorem solution {n oa ob : ℕ} (H₀ H₁ H₂ : Game n oa ob) (q₁ q₂ : ℕ) (t₁ t₂ ε₁ ε₂ : ℝ)
    (h₀₁ : Indist H₀ H₁ q₁ t₁ ε₁) (h₁₂ : Indist H₁ H₂ q₂ t₂ ε₂) :
    Indist H₀ H₂ (min q₁ q₂) (min t₁ t₂) (ε₁ + ε₂) := by
  intro A hA ht hq
  have a := h₀₁ A hA (le_trans ht (min_le_left _ _)) (le_trans hq (min_le_left _ _))
  have b := h₁₂ A hA (le_trans ht (min_le_right _ _)) (le_trans hq (min_le_right _ _))
  unfold adv at a b ⊢
  calc |H₀.prOne A - H₂.prOne A| ≤ |H₀.prOne A - H₁.prOne A| + |H₁.prOne A - H₂.prOne A| :=
        abs_sub_le _ _ _
    _ < ε₁ + ε₂ := add_lt_add a b
