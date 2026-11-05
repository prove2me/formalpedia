-- Prove2me | solution 1 for GeneralPieces.TopDisplay.logb_pow_le_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:07:18.005562+00:00
-- url     : https://prove2.me/submissions/32c9f0be-5113-4fb7-9582-424077264fde

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
theorem _root_.solution (t : ℝ) (ht : 1 ≤ t) (n : ℕ) : Real.logb 2 t ^ n ≤ (n.factorial * 2 ^ n : ℕ) * t := by
  have ht0 : 0 < t := by linarith
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have h1 := Real.pow_div_factorial_le_exp (Real.log t) hlog n
  rw [Real.exp_log ht0] at h1
  have h2 : Real.log t ^ n ≤ n.factorial * t := by rwa [div_le_iff₀' (by positivity)] at h1
  have h3 : Real.logb 2 t ≤ 2 * Real.log t := by
    rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
    have h2' : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith
  have h4 : 0 ≤ Real.logb 2 t := Real.logb_nonneg (by norm_num) ht
  calc Real.logb 2 t ^ n ≤ (2 * Real.log t) ^ n := pow_le_pow_left₀ h4 h3 n
    _ = 2 ^ n * Real.log t ^ n := mul_pow _ _ _
    _ ≤ 2 ^ n * (n.factorial * t) := by gcongr
    _ = (n.factorial * 2 ^ n : ℕ) * t := by push_cast; ring
end GeneralPieces.TopDisplay
