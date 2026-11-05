-- Prove2me | solution 1 for Groundwork.Grid.nodeC_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:56:16.624889+00:00
-- url     : https://prove2.me/submissions/f6ecb275-7954-4568-92a8-5aec76dba0f5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_CutWord
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_StepMachines_Prog_Brute
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_StepMachines_Math_SideCodes
import Theorems.Thm_Groundwork_Code_full_blocks
import Theorems.Thm_Groundwork_Code_full_cast
import Theorems.Thm_Groundwork_Grid_bitsC_full


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
namespace Groundwork.Grid
theorem _root_.solution (g : ℕ) (tr : Bool) (n : ℕ) : (nodeC g tr n).Full :=
  Code.full_cast _ _ _ (Code.full_blocks _ _ (bitsC_full n))
end Groundwork.Grid
