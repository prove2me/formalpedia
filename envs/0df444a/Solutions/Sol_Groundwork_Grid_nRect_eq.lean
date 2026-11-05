-- Prove2me | solution 1 for Groundwork.Grid.nRect_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:06:56.259434+00:00
-- url     : https://prove2.me/submissions/a1ae5e2f-eb82-4a2b-a74d-ecac7d7700b6

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
theorem _root_.solution (g : ℕ) : nRect g = c2 g * c2 g := by
  unfold nRect c2
  rw [Nat.choose_two_right, sq]
end Groundwork.Grid
