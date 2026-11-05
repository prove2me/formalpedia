-- Prove2me | solution 1 for Groundwork.colLabels_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:06:55.442444+00:00
-- url     : https://prove2.me/submissions/6e0afe56-d436-4bad-92ad-cf5186886d65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Math_CodeMore
import Definitions.Def_StepMachines_Math_Sparse

set_option autoImplicit false
section
section
open Groundwork
open Finset
open Groundwork.Prog (tb capW)
namespace Groundwork
theorem _root_.solution (n i : ℕ) : colLabels n i = sparseLab (false, false) n i := rfl
end Groundwork
