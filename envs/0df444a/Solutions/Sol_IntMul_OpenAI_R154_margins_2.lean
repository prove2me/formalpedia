-- Prove2me | solution 2 for IntMul.OpenAI.R154.margins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T21:02:25.52026+00:00
-- url     : https://prove2.me/submissions/e4046ae1-10df-468d-869c-0afd67a4f0a2

import Mathlib
import Definitions.Def_IntMul_OpenAI_R154

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open Real

namespace IntMul.OpenAI.R154.Pf

open IntMul.OpenAI.R154

/-! ## Margins -/

theorem margins' :
    2 * κ ≤ 1 - ε * (1 + c) ∧ 2 * κ ≤ ε * c * (1 - τ) ∧ 2 * κ ≤ ε * (1 - lam') ∧
      2 * κ ≤ 1 - τ - ε * (2 - τ) ∧ 2 * κ ≤ 1 / 4 - δ - 3 * ε / 2 ∧ 2 * κ ≤ 1 - δ - ε ∧
      2 * κ ≤ ε ∧ τ * (1 + c / (1 / 2)) < lam' ∧ lam' < 1 ∧ 0 < lam' - τ - c := by
  unfold κ ε c τ lam' δ
  norm_num

end IntMul.OpenAI.R154.Pf

section
open IntMul.OpenAI.R154

theorem solution :
    2 * κ ≤ 1 - ε * (1 + c) ∧ 2 * κ ≤ ε * c * (1 - τ) ∧ 2 * κ ≤ ε * (1 - lam') ∧
      2 * κ ≤ 1 - τ - ε * (2 - τ) ∧ 2 * κ ≤ 1 / 4 - δ - 3 * ε / 2 ∧ 2 * κ ≤ 1 - δ - ε ∧
      2 * κ ≤ ε ∧ τ * (1 + c / (1 / 2)) < lam' ∧ lam' < 1 ∧ 0 < lam' - τ - c :=
  IntMul.OpenAI.R154.Pf.margins'

end
