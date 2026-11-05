-- Prove2me | solution 1 for Groundwork.Grid.two_mul_c2_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:12:06.691956+00:00
-- url     : https://prove2.me/submissions/f1b04365-fdcc-44ef-b0f5-f133160bdd17

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_Digits

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect)
namespace Groundwork.Grid
theorem _root_.solution (g : ℕ) : 2 * c2 g ≤ g ^ 2 := by
  calc 2 * (g * (g - 1) / 2) ≤ g * (g - 1) := Nat.mul_div_le _ _
    _ ≤ g * g := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = g ^ 2 := (sq g).symm
end Groundwork.Grid
