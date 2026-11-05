-- Prove2me | solution 1 for GeneralPieces.Chain.num_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:44:36.175087+00:00
-- url     : https://prove2.me/submissions/8f9cbcec-2a46-453f-8d4f-846498786432

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Gen_Chain
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Rec_Chain
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_P2M_ClauseBound_Gen_pow_x__e84650c3cb9c


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Chain
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c : ℕ}
namespace GeneralPieces.Chain
theorem _root_.solution (x₀ : ℕ) (hx : 18 ≤ x₀) : 1.4 * (3 * (x₀ : ℝ) + 6) ≤ 2 ^ (x₀ - 9) := by
  have h1 := pow_x₀ x₀ hx
  have e : 2 ^ x₀ = 2 ^ (x₀ - 9) * 2 ^ 9 := by rw [← pow_add]; congr 1; omega
  rw [e] at h1
  have h2 : 2 * (3 * x₀ + 6) ≤ 2 ^ (x₀ - 9) := by
    generalize 2 ^ (x₀ - 9) = w at h1 ⊢
    omega
  have h3 : ((2 * (3 * x₀ + 6) : ℕ) : ℝ) ≤ ((2 ^ (x₀ - 9) : ℕ) : ℝ) := Nat.cast_le.2 h2
  push_cast at h3
  have h4 : (0 : ℝ) ≤ x₀ := Nat.cast_nonneg _
  linarith
end GeneralPieces.Chain
