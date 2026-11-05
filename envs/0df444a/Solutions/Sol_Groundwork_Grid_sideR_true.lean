-- Prove2me | solution 1 for Groundwork.Grid.sideR_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:12:16.742588+00:00
-- url     : https://prove2.me/submissions/4c4cd388-eec5-4e72-b5cd-45171527d5b0

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
theorem _root_.solution (g n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) : sideR g true n Rm = trInst (sideR g false n Rm) := by
  rfl
end Groundwork.Grid
