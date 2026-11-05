-- Prove2me | solution 1 for Groundwork.Grid.stC_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:57:54.492204+00:00
-- url     : https://prove2.me/submissions/ec57e72e-bd59-46ca-ad46-b32e03622605

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_CutWord
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_StepMachines_Prog_Brute
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_StepMachines_Math_SideCodes
import Theorems.Thm_Groundwork_Grid_nodeC_full
import Theorems.Thm_Groundwork_Code_full_blocks
import Theorems.Thm_Groundwork_Code_full_cast


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
namespace Groundwork.Grid
theorem _root_.solution (g : ℕ) (tr : Bool) (n : ℕ) : (stC g tr n).Full :=
  Code.full_cast _ _ _ (Code.full_blocks _ _ (nodeC_full g tr n))
end Groundwork.Grid
