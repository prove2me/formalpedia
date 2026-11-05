-- Prove2me | solution 1 for Groundwork.Grid.vC_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:06:57.274098+00:00
-- url     : https://prove2.me/submissions/e1978134-977a-4c9b-bd88-fef2d0cc5ec2

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
theorem _root_.solution (g n : ℕ) : (vC g n).Full := Code.full_cast _ _ _ (Code.full_blocks _ _ (bitsC_full n))
end Groundwork.Grid
