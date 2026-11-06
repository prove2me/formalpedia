-- Prove2me | solution 1 for GeneralPieces.Count.count_second
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:18:18.515285+00:00
-- url     : https://prove2.me/submissions/f753c9b5-5400-4bcb-825d-cde1a60de9d3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_Remarks
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_GeneralPieces_Rec_Count

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Count
open Levels.Gen ClauseBound.Gen
namespace GeneralPieces.Count
theorem _root_.solution (X T x y z : ℝ) (A G C₄ k2 Z : ℕ) (hX : 0 < X) (hT : T ≤ (2 : ℝ) ^ x * X ^ (A + k2 + Z)) (hxyz : x + y ≤ z) :
    X ^ (A + G + C₄) * T * (2 : ℝ) ^ y ≤ (2 : ℝ) ^ z * X ^ (2 * A + G + k2 + C₄ + Z) := by
  have h1 : (2 : ℝ) ^ x * (2 : ℝ) ^ y ≤ (2 : ℝ) ^ z := by
    rw [← Real.rpow_add (by norm_num)]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hxyz
  have hy : (0 : ℝ) < (2 : ℝ) ^ y := Real.rpow_pos_of_pos (by norm_num) _
  calc X ^ (A + G + C₄) * T * (2 : ℝ) ^ y ≤ X ^ (A + G + C₄) * ((2 : ℝ) ^ x * X ^ (A + k2 + Z)) * (2 : ℝ) ^ y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT (by positivity)) hy.le
    _ = ((2 : ℝ) ^ x * (2 : ℝ) ^ y) * X ^ (2 * A + G + k2 + C₄ + Z) := by ring
    _ ≤ (2 : ℝ) ^ z * X ^ (2 * A + G + k2 + C₄ + Z) := mul_le_mul_of_nonneg_right h1 (by positivity)
end GeneralPieces.Count
