-- Prove2me | solution 1 for GeneralPieces.TopDisplay.logb_le_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:37.805857+00:00
-- url     : https://prove2.me/submissions/aecb19ad-7709-42ca-acc4-f42faf84b1a0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA
namespace GeneralPieces.TopDisplay
theorem _root_.solution (y : ℝ) (hy : 1 ≤ y) : Real.logb 2 y ≤ 2 * y := by
  have h1 : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have h2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h3 : 0 < Real.log 2 := by linarith
  rw [Real.logb, div_le_iff₀ h3]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y) (sub_nonneg.mpr h2)]
end GeneralPieces.TopDisplay
