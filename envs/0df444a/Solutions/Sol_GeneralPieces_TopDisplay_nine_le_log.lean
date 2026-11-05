-- Prove2me | solution 1 for GeneralPieces.TopDisplay.nine_le_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:05:59.798271+00:00
-- url     : https://prove2.me/submissions/d7454d14-3af5-4142-99dd-8f225011368a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Theorems.Thm_ClauseBound_Alg_TopArith_le_logb_of_pow_le


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA
variable {K k m : ℕ}
namespace GeneralPieces.TopDisplay
theorem _root_.solution (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) : (9 : ℝ) ≤ Real.logb 2 ((k : ℝ) * m) := by
  have h1 : 2 ^ 9 ≤ k * m :=
    calc 2 ^ 9 ≤ K ^ 9 := Nat.pow_le_pow_left hK 9
      _ ≤ m := hm
      _ ≤ k * m := Nat.le_mul_of_pos_left _ hk
  have := le_logb_of_pow_le (k * m) 9 h1
  push_cast at this
  exact this
end GeneralPieces.TopDisplay
