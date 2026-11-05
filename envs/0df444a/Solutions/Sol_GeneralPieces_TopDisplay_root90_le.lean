-- Prove2me | solution 1 for GeneralPieces.TopDisplay.root90_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:34.390006+00:00
-- url     : https://prove2.me/submissions/a0b8b263-b37c-458b-b422-5e670d160ee9

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
theorem _root_.solution (K m : ℕ) (h : m ≤ K ^ 90) : (m : ℝ) ^ (1 / 90 : ℝ) ≤ K := by
  have h1 : (m : ℝ) ≤ (K : ℝ) ^ 90 := by exact_mod_cast h
  calc (m : ℝ) ^ (1 / 90 : ℝ) ≤ ((K : ℝ) ^ 90) ^ (1 / 90 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    _ = K := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
end GeneralPieces.TopDisplay
