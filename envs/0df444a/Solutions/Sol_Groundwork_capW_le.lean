-- Prove2me | solution 1 for Groundwork.capW_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:07:05.507132+00:00
-- url     : https://prove2.me/submissions/d4f3725d-7191-4584-bbf1-e63f1b62a8cb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Math_CodeMore
import Definitions.Def_StepMachines_Math_Sparse
import Theorems.Thm_Groundwork_Prog_tb_le


set_option autoImplicit false
section
section
open Groundwork
open Finset
open Groundwork.Prog (tb capW)
namespace Groundwork
theorem _root_.solution {n c : ℕ} (hn : 1 ≤ n) (hc : c ≤ n) : capW n c ≤ 4 * n := by
  have := Prog.tb_le c
  unfold capW
  omega
end Groundwork
