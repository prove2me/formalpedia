-- Prove2me | solution 1 for Groundwork.Prog.side_size_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:11:33.206808+00:00
-- url     : https://prove2.me/submissions/5e3ced44-3f21-41a9-b90f-7a50dd054155

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
theorem _root_.solution {g S X Z : ℕ} (h : Z ≤ S + sideA g * X) : Z ≤ S + sideA g * X ^ sideA g :=
  h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_self_pow (by unfold sideA; omega) X)) _)
end Groundwork.Prog
