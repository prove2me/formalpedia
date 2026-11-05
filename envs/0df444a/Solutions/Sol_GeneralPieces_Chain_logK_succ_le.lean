-- Prove2me | solution 1 for GeneralPieces.Chain.logK_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:49:15.638333+00:00
-- url     : https://prove2.me/submissions/b5dceabc-d707-4e6c-8d06-6382f9c25713

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Gen_Chain
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Rec_Chain
import Theorems.Thm_GeneralPieces_PartA_logK_formula


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Chain
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c : ℕ}
namespace GeneralPieces.Chain
theorem _root_.solution (x₀ l : ℕ) : 0.7 * Real.logb 2 (K x₀ (l + 1)) ≤ 1.4 * (3 * x₀ + 6) * 2 ^ l := by
  have h1 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have h2 : (0 : ℝ) ≤ x₀ := Nat.cast_nonneg x₀
  rw [PartA.logK_formula, pow_succ]
  push_cast
  linarith
end GeneralPieces.Chain
