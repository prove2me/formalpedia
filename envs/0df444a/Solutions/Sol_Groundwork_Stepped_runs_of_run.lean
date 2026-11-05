-- Prove2me | solution 1 for Groundwork.Stepped.runs_of_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:42:07.999574+00:00
-- url     : https://prove2.me/submissions/5c58e28e-29ae-48bc-a3ff-db9e5cfa0747

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
import Theorems.Thm_Groundwork_Stepped_next_iterate_of_out

set_option autoImplicit false
section
open Groundwork
open Groundwork.Stepped
variable {α β γ τ : Type}
namespace Groundwork.Stepped
theorem _root_.solution {M : Stepped α β} {S t : ℕ} {a : α} {b : β} (ho : M.out (M.run a t) = some b)
    (hs : ∀ n, size (M.run a n) ≤ S) : M.Runs a t S b := by
  unfold Runs run at *
  generalize M.init a = s at ho hs
  induction t generalizing s with
  | zero => exact .halt ho (hs 0)
  | succ t ih =>
    cases h : M.out s with
    | some b' =>
      rw [next_iterate_of_out h, h] at ho
      exact .halt (h.trans ho) (hs 0)
    | none =>
      have e : M.next s = M.step s := by rw [next, h]
      refine .step h (hs 0) (ih _ ?_ fun n => ?_)
      · rwa [Function.iterate_succ_apply, e] at ho
      · have := hs (n + 1)
        rwa [Function.iterate_succ_apply, e] at this
end Groundwork.Stepped
