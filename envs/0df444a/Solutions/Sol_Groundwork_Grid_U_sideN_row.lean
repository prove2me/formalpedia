-- Prove2me | solution 1 for Groundwork.Grid.U_sideN_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:15:04.157192+00:00
-- url     : https://prove2.me/submissions/9fd8558f-7eaf-48b8-adb2-d0926afb3732

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideCodes
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_StepMachines_Math_Pull
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_StepMachines_Math_SideNet
import Theorems.Thm_Groundwork_Grid_U_rowNet
import Theorems.Thm_P2M_Groundwork_Grid_sum___ixOf_e2b52bf0c490


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect tb capW priceRow priceCol BoundedInst SideNet)
namespace Groundwork.Grid
theorem _root_.solution (g n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) :
    (sideN g false n Rm y).U = g ^ 2 * (g - 1) * n + priceRow g n y := by
  change (sideNet g false n (sideR g false n Rm) y).U = _
  unfold sideNet priceRow
  rw [U_rowNet (Fintype.card_fin g) (Fintype.card_fin g), ← sum_Ω_ixOf]
  rfl
end Groundwork.Grid
