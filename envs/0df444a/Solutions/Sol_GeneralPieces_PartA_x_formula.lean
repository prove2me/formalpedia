-- Prove2me | solution 1 for GeneralPieces.PartA.x_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:14:55.861328+00:00
-- url     : https://prove2.me/submissions/06f3555b-3468-447f-b2a0-04fee6bb1ff3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Num_PartA

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartA
open Finset Levels.Gen ClauseBound.Gen
namespace GeneralPieces.PartA
theorem _root_.solution (x₀ l : ℕ) : (x x₀ l : ℝ) = (3 * x₀ + 6) * 2 ^ l - 6 * l - 2 * x₀ - 6 := by
  induction l with
  | zero => simp only [x]; push_cast; ring
  | succ l ih => rw [x_succ]; push_cast; rw [ih, pow_succ]; ring
end GeneralPieces.PartA
