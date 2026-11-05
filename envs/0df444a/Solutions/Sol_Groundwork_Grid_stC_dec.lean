-- Prove2me | solution 1 for Groundwork.Grid.stC_dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:39:52.427526+00:00
-- url     : https://prove2.me/submissions/658b63e6-99da-4d16-9876-5772c32d346e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_CutWord
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_StepMachines_Prog_Brute
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_StepMachines_Math_SideCodes
import Theorems.Thm_Groundwork_Grid_gridE_symm_val

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
namespace Groundwork.Grid
theorem _root_.solution (g : ℕ) (tr : Bool) (n : ℕ) (z : List Bool) (x : Fin g) (w' : Fin g × Fin g) :
    (stC g tr n).dec z x w' = bitsOf n (he g n z x (node g tr w'.1 w'.2)) := by
  rw [← gridE_symm_val]
  rfl
end Groundwork.Grid
