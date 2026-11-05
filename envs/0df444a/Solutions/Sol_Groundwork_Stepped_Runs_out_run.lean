-- Prove2me | solution 1 for Groundwork.Stepped.Runs.out_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:41:53.7992+00:00
-- url     : https://prove2.me/submissions/b5dceff7-c599-480d-bdea-05d2fe39ca39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
import Theorems.Thm_Groundwork_Stepped_Reaches_iterate

set_option autoImplicit false
section
open Groundwork
open Groundwork.Stepped
variable {α β γ τ : Type}
namespace Groundwork.Stepped
namespace Runs
theorem _root_.solution {M : Stepped α β} {S t : ℕ} {a : α} {b : β} (h : M.Runs a t S b) {T : ℕ}
    (hT : t ≤ T) : M.out (M.run a T) = some b := (Reaches.iterate h).1 T hT
end Runs
end Groundwork.Stepped
