-- Prove2me | solution 1 for Groundwork.Stepped.next_iterate_of_out
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:02:31.649087+00:00
-- url     : https://prove2.me/submissions/1808960e-93d3-43b5-b3a3-7e3fed16e47b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped

set_option autoImplicit false
section
open Groundwork
open Groundwork.Stepped
variable {α β γ τ : Type}
namespace Groundwork.Stepped
theorem _root_.solution {M : Stepped α β} {s : M.σ} {b : β} (h : M.out s = some b) (n : ℕ) :
    M.next^[n] s = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, next, h]
end Groundwork.Stepped
