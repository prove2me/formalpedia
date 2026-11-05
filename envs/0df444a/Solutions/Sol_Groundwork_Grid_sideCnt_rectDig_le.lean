-- Prove2me | solution 1 for Groundwork.Grid.sideCnt_rectDig_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:08:01.05272+00:00
-- url     : https://prove2.me/submissions/837791ac-034e-48b2-83e7-274e747f673e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideCodes
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_StepMachines_Math_Pull
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_StepMachines_Math_SideNet
import Theorems.Thm_Groundwork_Grid_digit_le
import Theorems.Thm_Groundwork_Prog_digit_le


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect tb capW priceRow priceCol BoundedInst SideNet)
namespace Groundwork.Grid
theorem _root_.solution (g : ℕ) (tr : Bool) (n y p κ : ℕ) : sideCnt tr n (rectDig g tr n y p κ) ≤ n := by
  have h : rectDig g tr n y p κ ≤ n := digit_le _ _ _
  unfold sideCnt
  split_ifs <;> omega
end Groundwork.Grid
