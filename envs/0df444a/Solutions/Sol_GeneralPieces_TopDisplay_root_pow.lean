-- Prove2me | solution 1 for GeneralPieces.TopDisplay.root_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:06:48.10865+00:00
-- url     : https://prove2.me/submissions/24661a57-c3a3-4e4c-b8bc-2bb8b73f6b37

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
theorem _root_.solution (m d : ℕ) (hd : 1 ≤ d) : ((m : ℝ) ^ (1 / (9 * d : ℝ))) ^ (9 * d) = m := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have : 1 / (9 * (d : ℝ)) * ((9 * d : ℕ) : ℝ) = 1 := by push_cast; field_simp
  rw [this, Real.rpow_one]
end GeneralPieces.TopDisplay
