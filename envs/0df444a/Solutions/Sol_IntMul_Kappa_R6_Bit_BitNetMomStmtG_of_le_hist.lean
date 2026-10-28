-- Prove2me | solution 1 for IntMul.Kappa.R6.Bit.BitNetMomStmtG_of_le_hist
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:31:46.358995+00:00
-- url     : https://prove2.me/submissions/2f276c84-5149-4742-87fd-43ab140698a3

import Definitions.Def_IntMul_Kappa_RG_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa IntMul.Kappa.R6.Bit

theorem solution (Wb mb : ℕ) (h₁ h₂ : List (ℕ × ℕ))
    (hle : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → histMoment h₁ mb τ ≤ histMoment h₂ mb τ) :
    BitNetMomStmtG Wb mb h₁ → BitNetMomStmtG Wb mb h₂ := by
  intro h
  obtain ⟨T, C, q₀, hRun, hOK, hmom⟩ := h
  refine ⟨T, C, q₀, hRun, hOK, fun τ hτ₀ hτ₁ => (hmom τ hτ₀ hτ₁).trans (hle τ hτ₀ hτ₁)⟩
