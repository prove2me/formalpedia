-- Prove2me | solution 1 for Groundwork.Prog.tb_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:39:49.63421+00:00
-- url     : https://prove2.me/submissions/f115e4db-b3f5-4743-b519-9fe47a57033b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Math_GridArith
import Definitions.Def_StepMachines_Prog_GridDefs

set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped
namespace Groundwork.Prog
theorem _root_.solution (c : ℕ) : tb c ≤ 2 * c + 1 := by
  unfold tb
  rw [Nat.size_le]
  calc 3 ^ c ≤ 4 ^ c := Nat.pow_le_pow_left (by norm_num) c
    _ = 2 ^ (2 * c) := by rw [pow_mul]; norm_num
    _ < 2 ^ (2 * c + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
end Groundwork.Prog
