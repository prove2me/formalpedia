-- Prove2me | solution 1 for Groundwork.Grid.sideN_sized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:21:47.616007+00:00
-- url     : https://prove2.me/submissions/45431e41-8466-41ce-aa01-c27d804fe660

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideCodes
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_StepMachines_Math_Pull
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_StepMachines_Math_SideNet
import Theorems.Thm_Groundwork_Grid_sideNet_sized
import Theorems.Thm_Groundwork_Grid_abs_sideR_le
import Theorems.Thm_Groundwork_Network_sized_pull_of_le


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect tb capW priceRow priceCol BoundedInst SideNet)
namespace Groundwork.Grid
theorem _root_.solution {g n B : ℕ} (tr : Bool) (hn : 1 ≤ n) {Rm : Inst (Fin (g * g)) (List Bool)} (hR : BoundedInst n B Rm)
    (y : ℕ) : (sideN g tr n Rm y).Sized (2 * g ^ 3 * n) (g * B + g ^ 2 * n) :=
  Network.sized_pull_of_le _ _ _ _ (sideNet_sized tr hn (abs_sideR_le tr hR) y) fun _ => by
    rw [Nat.mul_assoc]; omega
end Groundwork.Grid
