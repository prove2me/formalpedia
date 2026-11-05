-- Prove2me | solution 1 for GeneralPieces.PartA.K_ge_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:15:08.27422+00:00
-- url     : https://prove2.me/submissions/465bc1a3-89d6-44fc-8775-ee1f1b7996b9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Num_PartA
import Theorems.Thm_ClauseBound_Gen_K_eq


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartA
open Finset Levels.Gen ClauseBound.Gen
namespace GeneralPieces.PartA
theorem _root_.solution (x₀ l : ℕ) (hx : 18 ≤ x₀) : 2 ^ (18 * (l + 1)) ≤ K x₀ l := by
  have h1 : l + 1 ≤ 2 ^ l := Nat.lt_two_pow_self
  have h2 : (l + 1) * 18 ≤ 2 ^ l * x₀ := Nat.mul_le_mul h1 hx
  have h3 := x_ge_pow x₀ l
  rw [K_eq]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)
end GeneralPieces.PartA
