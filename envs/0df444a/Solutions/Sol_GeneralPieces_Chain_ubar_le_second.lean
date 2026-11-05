-- Prove2me | solution 1 for GeneralPieces.Chain.ubar_le_second
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:44:05.029807+00:00
-- url     : https://prove2.me/submissions/4cce1294-26bb-432d-845c-20d8f4851e75

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Gen_Chain
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Rec_Chain
import Theorems.Thm_ClauseBound_Gen_Rate_four_nRect_le


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Chain
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c : ℕ}
namespace GeneralPieces.Chain
theorem _root_.solution (hP : Par P ρ c) (x₀ l lam : ℕ) (hlam : 1 ≤ lam) :
    (g x₀ l : ℝ) ^ 4 * lam / g x₀ l + nRectG (g x₀ l) (g x₀ l) * (4 * ρ * lam + c * Real.logb 2 (2 * lam)) ≤
      (g x₀ l : ℝ) ^ 4 * lam * (ρ + 1 / g x₀ l) + c / 4 * (g x₀ l : ℝ) ^ 4 * Real.logb 2 (2 * lam) := by
  have hR : (nRectG (g x₀ l) (g x₀ l) : ℝ) ≤ (g x₀ l : ℝ) ^ 4 / 4 := by
    have : ((4 * nRectG (g x₀ l) (g x₀ l) : ℕ) : ℝ) ≤ ((g x₀ l ^ 4 : ℕ) : ℝ) := by exact_mod_cast four_nRect_le (g x₀ l)
    push_cast at this
    linarith
  have h0 : 0 ≤ 4 * ρ * lam + c * Real.logb 2 (2 * lam) := le_trans (Nat.cast_nonneg _) (hP.caps 0 lam hlam)
  have h1 := mul_le_mul_of_nonneg_right hR h0
  have e1 : (g x₀ l : ℝ) ^ 4 * lam * (ρ + 1 / g x₀ l) + c / 4 * (g x₀ l : ℝ) ^ 4 * Real.logb 2 (2 * lam) =
      (g x₀ l : ℝ) ^ 4 * lam / g x₀ l + (g x₀ l : ℝ) ^ 4 / 4 * (4 * ρ * lam + c * Real.logb 2 (2 * lam)) := by ring
  rw [e1]
  exact add_le_add_right h1 _
end GeneralPieces.Chain
