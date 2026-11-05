-- Prove2me | solution 1 for GeneralPieces.Chain.hoeffding_cond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:10.398706+00:00
-- url     : https://prove2.me/submissions/5797cd00-142c-4661-934a-c2395be46a5e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Gen_Chain
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Rec_Chain
import Theorems.Thm_GeneralPieces_Chain_two_zeta_sq_g
import Theorems.Thm_GeneralPieces_Chain_log_two_gK_le
import Theorems.Thm_GeneralPieces_Chain_logK_succ_le
import Theorems.Thm_GeneralPieces_Chain_num_le
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Chain
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c : ℕ}
namespace GeneralPieces.Chain
theorem _root_.solution (x₀ l : ℕ) (hx : 18 ≤ x₀) : (K x₀ l : ℝ) * Real.log (2 * g x₀ l * K x₀ l) ≤ 2 * zeta l ^ 2 * g x₀ l := by
  rw [two_zeta_sq_g x₀ l (by omega), mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
  calc Real.log (2 * g x₀ l * K x₀ l) ≤ 0.7 * Real.logb 2 (K x₀ (l + 1)) := log_two_gK_le x₀ l hx
    _ ≤ 1.4 * (3 * x₀ + 6) * 2 ^ l := logK_succ_le x₀ l
    _ ≤ 2 ^ (x₀ - 9) * 2 ^ l := mul_le_mul_of_nonneg_right (num_le x₀ hx) (by positivity)
    _ = 2 ^ (l + x₀ - 9) := by rw [← pow_add]; congr 1; omega
end GeneralPieces.Chain
