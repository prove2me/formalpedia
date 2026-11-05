-- Prove2me | solution 1 for GeneralPieces.PartA.exp_tsum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:56:59.672707+00:00
-- url     : https://prove2.me/submissions/3f7993cb-a174-40da-b2d5-b1e3907e4615

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Num_PartA
import Theorems.Thm_GeneralPieces_PartA_hasSum_a
import Theorems.Thm_GeneralPieces_PartA_hasSum_b

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartA
open Finset Levels.Gen ClauseBound.Gen
namespace GeneralPieces.PartA
theorem _root_.solution : Real.exp (∑' j : ℕ, (1 : ℝ) / 2 ^ (j + 2)) * (1 / 2 + ∑' j : ℕ, (6 : ℝ) * 2 ^ j / 2 ^ (18 * (j + 1))) ≤
    Real.exp (1 / 2) * 0.51 := by
  rw [hasSum_a.tsum_eq, hasSum_b.tsum_eq]
  exact mul_le_mul_of_nonneg_left (by norm_num) (Real.exp_pos _).le
end GeneralPieces.PartA
