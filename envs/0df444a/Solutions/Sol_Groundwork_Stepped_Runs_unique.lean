-- Prove2me | solution 1 for Groundwork.Stepped.Runs.unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:42:48.230225+00:00
-- url     : https://prove2.me/submissions/b75375cb-bc3d-4ca1-83d5-0142b48d09f3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
import Theorems.Thm_Groundwork_Stepped_Runs_out_run

set_option autoImplicit false
section
open Groundwork
open Groundwork.Stepped
variable {α β γ τ : Type}
namespace Groundwork.Stepped
namespace Runs
theorem _root_.solution {M : Stepped α β} {S S' t t' : ℕ} {a : α} {b b' : β} (h : M.Runs a t S b)
    (h' : M.Runs a t' S' b') : b = b' := by
  have h1 := h.out_run (le_max_left t t')
  have h2 := h'.out_run (le_max_right t t')
  exact Option.some.inj (h1.symm.trans h2)
end Runs
end Groundwork.Stepped
