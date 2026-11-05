-- Prove2me | solution 1 for GeneralPieces.PartA.hasSum_a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:15:09.427913+00:00
-- url     : https://prove2.me/submissions/c4cd37a5-c206-4329-a07b-c3bce1384097

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
theorem _root_.solution : HasSum (fun j : ℕ => (1 : ℝ) / 2 ^ (j + 2)) (1 / 2) := by
  have h := hasSum_geometric_two.mul_left (1 / 4 : ℝ)
  have hf : (fun j : ℕ => (1 : ℝ) / 2 ^ (j + 2)) = fun j : ℕ => 1 / 4 * (1 / 2) ^ j := by
    funext j; rw [pow_add, one_div_pow]; field_simp; norm_num
  rw [hf]
  have h2 : (1 / 4 : ℝ) * 2 = 1 / 2 := by norm_num
  rwa [h2] at h
end GeneralPieces.PartA
