-- Prove2me | solution 1 for Groundwork.Grid.ZW_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:16:06.181685+00:00
-- url     : https://prove2.me/submissions/71f47bf1-c972-4acb-ad73-3f29318fbef1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideCodes
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_StepMachines_Math_Pull
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_StepMachines_Math_SideNet
import Theorems.Thm_Groundwork_Grid_ZG_cross_eq_sum
import Theorems.Thm_Groundwork_Grid_ZW_eq_Z
import Theorems.Thm_Groundwork_Grid_Z_eq_ZG_X
import Theorems.Thm_Groundwork_Grid_sum_patOf


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect tb capW priceRow priceCol BoundedInst SideNet)
namespace Groundwork.Grid
theorem _root_.solution (g n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) :
    Inst.ZW n [] Rm = ∑ y ∈ range ((n + 1) ^ nRect g), sideZ g n Rm y := by
  rw [ZW_eq_Z n Rm (fun _ => false), Z_eq_ZG_X _ _ (gridE g false), ZG_cross_eq_sum, ← sum_patOf]
  rfl
end Groundwork.Grid
