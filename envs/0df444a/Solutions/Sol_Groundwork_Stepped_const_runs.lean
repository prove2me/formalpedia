-- Prove2me | solution 1 for Groundwork.Stepped.const_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:24:30.342618+00:00
-- url     : https://prove2.me/submissions/8565d90d-e20b-4bfa-9021-8ed7ffbf619c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Comb
import Theorems.Thm_Groundwork_Stepped_ofFun_runs


set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
variable {α α₁ α₂ β γ δ ι : Type}
namespace Groundwork.Stepped
theorem _root_.solution [HasSize α] [HasSize β] (b : β) (a : α) :
    (const b : Stepped α β).Runs a 1 (max (size a) (size b) + 1) b := ofFun_runs _ a
end Groundwork.Stepped
