-- Prove2me | solution 1 for GeneralPieces.PartA.hasSum_b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:15:17.164121+00:00
-- url     : https://prove2.me/submissions/b6ce26a4-2101-4a21-9dc6-3e89eff7420d

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
theorem _root_.solution : HasSum (fun j : ℕ => (6 : ℝ) * 2 ^ j / 2 ^ (18 * (j + 1))) (6 / 2 ^ 18 * (1 - 1 / 2 ^ 17)⁻¹) := by
  have h := (hasSum_geometric_of_lt_one (r := (1 / 2 ^ 17 : ℝ)) (by positivity) (by norm_num)).mul_left (6 / 2 ^ 18 : ℝ)
  have hf : (fun j : ℕ => (6 : ℝ) * 2 ^ j / 2 ^ (18 * (j + 1))) = fun j : ℕ => 6 / 2 ^ 18 * (1 / 2 ^ 17) ^ j := by
    funext j
    rw [show 18 * (j + 1) = 18 + 17 * j + j by ring, pow_add, pow_add, pow_mul, one_div_pow]
    field_simp
  rw [hf]
  exact h
end GeneralPieces.PartA
