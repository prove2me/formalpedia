-- Prove2me | solution 1 for GeneralPieces.PartA.y_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:34:18.2897+00:00
-- url     : https://prove2.me/submissions/fa7c3a4d-536a-4fa2-bc53-00408eef4a72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Num_PartA
import Theorems.Thm_GeneralPieces_PartA_y_le_exp_tsum
import Theorems.Thm_GeneralPieces_PartA_exp_tsum_le
import Theorems.Thm_GeneralPieces_PartA_exp_half_mul_lt

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartA
open Finset Levels.Gen ClauseBound.Gen
namespace GeneralPieces.PartA
theorem _root_.solution (ρ : ℝ) (x₀ l : ℕ) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) : y ρ x₀ l < 0.85 :=
  lt_of_le_of_lt (le_trans (y_le_exp_tsum ρ x₀ l hρ hx) exp_tsum_le) exp_half_mul_lt
end GeneralPieces.PartA
