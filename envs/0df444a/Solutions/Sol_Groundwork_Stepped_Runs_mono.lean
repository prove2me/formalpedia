-- Prove2me | solution 1 for Groundwork.Stepped.Runs.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:21:10.338623+00:00
-- url     : https://prove2.me/submissions/9dc1311e-b200-473f-a253-bdca38ebab08

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
import Theorems.Thm_Groundwork_Stepped_Reaches_mono

set_option autoImplicit false
section
open Groundwork
open Groundwork.Stepped
variable {α β γ τ : Type}
namespace Groundwork.Stepped
namespace Runs
theorem _root_.solution {M : Stepped α β} {S S' t t' : ℕ} {a : α} {b : β} (h : M.Runs a t S b)
    (ht : t ≤ t') (hS : S ≤ S') : M.Runs a t' S' b := Reaches.mono h ht hS
end Runs
end Groundwork.Stepped
