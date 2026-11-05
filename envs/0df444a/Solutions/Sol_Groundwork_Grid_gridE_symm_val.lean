-- Prove2me | solution 1 for Groundwork.Grid.gridE_symm_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:38:32.957488+00:00
-- url     : https://prove2.me/submissions/87b3c75f-b61d-42d8-a9ff-276653d05f43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_CutWord
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_StepMachines_Prog_Brute
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_StepMachines_Math_SideCodes

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
namespace Groundwork.Grid
theorem _root_.solution (g : ℕ) (tr : Bool) (w : Fin g × Fin g) : ((gridE g tr).symm w : ℕ) = node g tr w.1 w.2 := by
  cases tr <;> rfl
end Groundwork.Grid
