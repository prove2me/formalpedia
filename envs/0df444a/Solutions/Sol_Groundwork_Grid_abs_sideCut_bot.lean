-- Prove2me | solution 1 for Groundwork.Grid.abs_sideCut_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:11:10.595098+00:00
-- url     : https://prove2.me/submissions/aebcb19d-367a-4127-9cef-6e30f30e8a86

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparse
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_CutWord
import Theorems.Thm_Groundwork_abs_colBot_le
import Theorems.Thm_Groundwork_abs_rowBot_le


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (tb capW)
namespace Groundwork.Grid
theorem _root_.solution (tr : Bool) (n i : ℕ) (u v : Bits n) (β : Fin n → Bell) : |(sideCut tr n i).bot u v β| ≤ 2 ^ n := by
  cases tr
  · exact abs_rowBot_le i β u v
  · exact abs_colBot_le i β u v
end Groundwork.Grid
