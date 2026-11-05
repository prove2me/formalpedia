-- Prove2me | solution 1 for Groundwork.Prog.sideA_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:11:24.404493+00:00
-- url     : https://prove2.me/submissions/57b82f85-511b-4a2a-a2b8-f3e475d287ea

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Side
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Prog_GridCount
import Definitions.Def_StepMachines_Prog_SidePresents

set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped
open Groundwork.Grid (he node c2 sideN sideCap)
namespace Groundwork.Prog
theorem _root_.solution (g X : ℕ) :
    sideA g * X = 4 * (g ^ 4 * X) + 8 * (g ^ 3 * X) + 20 * (g ^ 2 * X) + 20 * (g * X) + 1000 * X := by
  unfold sideA; ring
end Groundwork.Prog
