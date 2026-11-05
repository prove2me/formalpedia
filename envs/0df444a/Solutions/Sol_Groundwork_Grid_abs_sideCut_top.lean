-- Prove2me | solution 1 for Groundwork.Grid.abs_sideCut_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:10:31.691497+00:00
-- url     : https://prove2.me/submissions/df8e7df8-bcf3-4770-91ae-c9a340b0b454

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparse
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_CutWord
import Theorems.Thm_Groundwork_abs_colTop_le
import Theorems.Thm_Groundwork_abs_rowTop_le


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (tb capW)
namespace Groundwork.Grid
theorem _root_.solution (tr : Bool) (n i : ℕ) (x y : Bits n) (β : Fin n → Bell) : |(sideCut tr n i).top x y β| ≤ 2 ^ n := by
  have h1 : (1 : ℤ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  cases tr
  · exact (abs_rowTop_le β x y).trans h1
  · exact (abs_colTop_le β x y).trans h1
end Groundwork.Grid
