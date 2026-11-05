-- Prove2me | solution 1 for Groundwork.Grid.rectLen_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:09:24.659213+00:00
-- url     : https://prove2.me/submissions/83d7b077-719b-422b-96ff-d40aa55a0fed

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideCodes
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_StepMachines_Math_Pull
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_StepMachines_Math_SideNet
import Theorems.Thm_Groundwork_Grid_sideCnt_rectDig_le
import Theorems.Thm_Groundwork_Prog_tb_le


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect tb capW priceRow priceCol BoundedInst SideNet)
namespace Groundwork.Grid
theorem _root_.solution (g : ℕ) (tr : Bool) (n y p κ : ℕ) : rectLen g tr n y p κ ≤ 3 * n + 1 := by
  have h1 := sideCnt_rectDig_le g tr n y p κ
  have h2 := Prog.tb_le (sideCnt tr n (rectDig g tr n y p κ))
  unfold rectLen capW
  omega
end Groundwork.Grid
