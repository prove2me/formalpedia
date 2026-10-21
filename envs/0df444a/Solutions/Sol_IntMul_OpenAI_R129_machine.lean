-- Prove2me | solution 1 for IntMul.OpenAI.R129.machine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-20T13:45:09.082983+00:00
-- url     : https://prove2.me/submissions/a872bf11-1a11-4be1-860b-780826689e1c

import Definitions.Def_IntMul_OpenAI_R129
import Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFTop_kappa_bound

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Real

theorem solution : ∃ M : IntMul.MultitapeTM,
    (∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, IntMul.MultipliesAt M n T) ∧
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ A n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → IntMul.MultipliesAt M n
        (C₀ * (IntMul.OpenAI.Glue.VP n *
          IntMul.OpenAI.R129.Ncost (6 * (IntMul.lg n : ℝ)) (IntMul.OpenAI.R129.dP n) (IntMul.OpenAI.R129.KP n)
            (IntMul.OpenAI.R129.ℓP n) (IntMul.OpenAI.R129.αP n) *
            (Real.log (IntMul.lg n) + 1) ^ A + n)) :=
  IntMul.OpenAI.R129.P.NLogN.KFTop.kappa_bound
