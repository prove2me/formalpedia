-- Prove2me | solution 1 for NQueensComp.NPC.observation_29
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:32:43.05377+00:00
-- url     : https://prove2.me/submissions/9f8fc3a3-2a47-4022-a9c4-354e66de6263

import Mathlib
import Definitions.Def_NQueensComp_NPC_Queens

open NQueensComp.NPC

theorem solution (a₁ a₂ c₁ c₂ d₁ d₂ s₁ s₂ : ℤ)
    (ha₁ : 0 ≤ a₁ ∧ a₁ ≤ 2) (ha₂ : 0 ≤ a₂ ∧ a₂ ≤ 2) (hd₁ : 0 ≤ d₁ ∧ d₁ ≤ 6)
    (hd₂ : 0 ≤ d₂ ∧ d₂ ≤ 6) (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (h : 21 * (c₁ - c₂) + s₁ * (7 * (a₁ - a₂)) + s₂ * (d₁ - d₂) = 0) :
    c₁ = c₂ ∧ a₁ = a₂ ∧ d₁ = d₂ := by
  rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl <;> omega
