-- Prove2me | solution 1 for Groundwork.Grid.sideCl_D
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:16:53.198724+00:00
-- url     : https://prove2.me/submissions/eca1fdfd-810f-4d8f-ba63-c5e54c238235

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_StepMachines_Math_SideX

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {g n : ℕ}
namespace Groundwork.Grid
theorem _root_.solution (tr : Bool) (R : Inst (Fin g × Fin g) (Bits n)) (y : ℕ) {a b : Fin g} (hab : a < b) :
    (sideCl g tr n R y a b).D = ((vC g n).prod (rectsC g tr n y a b)).D := by
  unfold sideCl
  rw [dif_pos hab]
  rfl
end Groundwork.Grid
