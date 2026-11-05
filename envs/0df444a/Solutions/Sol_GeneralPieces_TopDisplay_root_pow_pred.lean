-- Prove2me | solution 1 for GeneralPieces.TopDisplay.root_pow_pred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:07:09.659803+00:00
-- url     : https://prove2.me/submissions/08425d8d-eace-43c8-ae11-0ba37463d62c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA
namespace GeneralPieces.TopDisplay
theorem _root_.solution (m d : ℕ) (hd : 1 ≤ d) : (m : ℝ) ^ (1 - 1 / (9 * d : ℝ)) = ((m : ℝ) ^ (1 / (9 * d : ℝ))) ^ (9 * d - 1) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  have : ((9 * d - 1 : ℕ) : ℝ) = 9 * d - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [this]; field_simp
end GeneralPieces.TopDisplay
