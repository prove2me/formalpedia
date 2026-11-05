-- Prove2me | solution 1 for GeneralPieces.Chain.log_two_gK_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:00:19.817616+00:00
-- url     : https://prove2.me/submissions/7c21115d-8a1d-4e21-a48e-b6dc0a21e2e0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Gen_Chain
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Rec_Chain
import Theorems.Thm_GeneralPieces_Chain_two_gK_le
import Theorems.Thm_ClauseBound_Gen_K_cast
import Theorems.Thm_ClauseBound_Gen_Rate_pow_le_g
import Theorems.Thm_ClauseBound_Gen_logb_K


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Chain
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c : ℕ}
namespace GeneralPieces.Chain
theorem _root_.solution (x₀ l : ℕ) (hx : 18 ≤ x₀) : Real.log (2 * g x₀ l * K x₀ l) ≤ 0.7 * Real.logb 2 (K x₀ (l + 1)) := by
  have h1 : (2 : ℝ) * g x₀ l * K x₀ l ≤ K x₀ (l + 1) := by exact_mod_cast two_gK_le x₀ l (by omega)
  have hK : (0 : ℝ) < K x₀ l := by rw [K_cast]; positivity
  have hg : (0 : ℝ) < g x₀ l := by
    have := pow_le_g hx l
    exact_mod_cast lt_of_lt_of_le (by positivity) this
  have h2 := Real.log_le_log (by positivity) h1
  have h3 : Real.log 2 ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
  rw [logb_K]
  rw [K_cast x₀ (l + 1), Real.log_pow] at h2
  have h4 : (x x₀ (l + 1) : ℝ) * Real.log 2 ≤ x x₀ (l + 1) * 0.7 := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
  linarith
end GeneralPieces.Chain
