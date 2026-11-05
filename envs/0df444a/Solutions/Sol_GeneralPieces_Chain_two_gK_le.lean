-- Prove2me | solution 1 for GeneralPieces.Chain.two_gK_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:44:12.509029+00:00
-- url     : https://prove2.me/submissions/1d7d8c99-5631-4e89-bf6e-037f9843b60c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Gen_Chain
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Rec_Chain
import Theorems.Thm_ClauseBound_Gen_Rate_K_succ


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Chain
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c : ℕ}
namespace GeneralPieces.Chain
theorem _root_.solution (x₀ l : ℕ) (hx : 1 ≤ x₀) : 2 * g x₀ l * K x₀ l ≤ K x₀ (l + 1) := by
  have h : 2 * K x₀ l ≤ g x₀ l := by
    unfold g
    refine Nat.mul_le_mul_right _ ?_
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (3 * l + x₀) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 2 * g x₀ l * K x₀ l = g x₀ l * (2 * K x₀ l) := by ring
    _ ≤ g x₀ l * g x₀ l := Nat.mul_le_mul_left _ h
    _ = K x₀ (l + 1) := by rw [K_succ, sq]
end GeneralPieces.Chain
