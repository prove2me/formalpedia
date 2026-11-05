-- Prove2me | solution 1 for Groundwork.Grid.bitsC_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:37:33.629908+00:00
-- url     : https://prove2.me/submissions/f80f7f17-0fde-4db9-97e4-a5253078696c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparse
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_CutWord

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (tb capW)
namespace Groundwork.Grid
theorem _root_.solution (n : ℕ) : (bitsC n).Full := rfl
end Groundwork.Grid
