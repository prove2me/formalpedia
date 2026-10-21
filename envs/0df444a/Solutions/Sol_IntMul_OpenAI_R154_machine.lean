-- Prove2me | solution 1 for IntMul.OpenAI.R154.machine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-20T08:08:57.426015+00:00
-- url     : https://prove2.me/submissions/9a7db3b7-8936-45bc-b262-97c22424998e

import Definitions.Def_IntMul_OpenAI_R154
import Theorems.Thm_IntMul_OpenAI_R154_P_NLogN_KFTop_kappa_bound

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Real

theorem solution : ∃ M : IntMul.MultitapeTM,
    (∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, IntMul.MultipliesAt M n T) ∧
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ A n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → IntMul.MultipliesAt M n
        (C₀ * (IntMul.OpenAI.Glue.VP n *
          IntMul.OpenAI.R154.Ncost (6 * (IntMul.lg n : ℝ)) (IntMul.OpenAI.R154.dP n) (IntMul.OpenAI.R154.KP n)
            (IntMul.OpenAI.R154.ℓP n) (IntMul.OpenAI.R154.αP n) *
            (Real.log (IntMul.lg n) + 1) ^ A + n)) :=
  IntMul.OpenAI.R154.P.NLogN.KFTop.kappa_bound
