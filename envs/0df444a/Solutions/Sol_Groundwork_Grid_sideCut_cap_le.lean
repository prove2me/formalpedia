-- Prove2me | solution 1 for Groundwork.Grid.sideCut_cap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:08:22.909188+00:00
-- url     : https://prove2.me/submissions/8d96e68f-cb8f-4523-a1ce-f5bb31a033bc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparse
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_CutWord
import Theorems.Thm_Groundwork_capW_le


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (tb capW)
namespace Groundwork.Grid
theorem _root_.solution (tr : Bool) {n i : ℕ} (hn : 1 ≤ n) (h : i ≤ n) : (sideCut tr n i).cap ≤ 2 * 2 * n := by
  have hc : sideCnt tr n i ≤ n := by
    cases tr
    · exact Nat.sub_le n i
    · exact h
  have h4 := capW_le hn hc
  change capW n (sideCnt tr n i) ≤ 2 * 2 * n
  omega
end Groundwork.Grid
