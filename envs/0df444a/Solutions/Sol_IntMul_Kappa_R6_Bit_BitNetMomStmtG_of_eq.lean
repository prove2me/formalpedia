-- Prove2me | solution 1 for IntMul.Kappa.R6.Bit.BitNetMomStmtG_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:24:47.801781+00:00
-- url     : https://prove2.me/submissions/3f8d183d-5d1f-4c48-af1f-0a877179417a

import Definitions.Def_IntMul_Kappa_RG_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa IntMul.Kappa.R6.Bit

theorem solution (Wb mb T q₀ : ℕ) (hb : List (ℕ × ℕ))
    (C : QHNet (ZMod 2) Wb T mb)
    (hRun : C.RunsOK)
    (hOK : ∀ q, q.Prime → q₀ < q → ∀ f, C.EdgesOK (q ^ f) ∧ C.FormalOK (q ^ f))
    (hmom : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → histMoment C.hist mb τ = histMoment hb mb τ) :
    BitNetMomStmtG Wb mb hb :=
  ⟨T, C, q₀, hRun, hOK, fun τ h₁ h₂ => (hmom τ h₁ h₂).le⟩
