-- Prove2me | solution 1 for GeneralPieces.PartA.two_pow_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:59:21.370599+00:00
-- url     : https://prove2.me/submissions/f0ae97e8-6489-4cc1-ab02-d5587980ff63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Num_PartA
import Theorems.Thm_GeneralPieces_PartA_x_formula

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartA
open Finset Levels.Gen ClauseBound.Gen
namespace GeneralPieces.PartA
theorem _root_.solution (x₀ l : ℕ) : (x x₀ l : ℝ) / (3 * x₀ + 6) ≤ 2 ^ l := by
  rw [div_le_iff₀ (by positivity), x_formula]
  have h1 : (0 : ℝ) ≤ l := by positivity
  have h2 : (0 : ℝ) ≤ x₀ := by positivity
  nlinarith
end GeneralPieces.PartA
