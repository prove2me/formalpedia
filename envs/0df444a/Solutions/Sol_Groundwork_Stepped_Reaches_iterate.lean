-- Prove2me | solution 1 for Groundwork.Stepped.Reaches.iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:03:47.024389+00:00
-- url     : https://prove2.me/submissions/19469ebe-897d-4a74-b369-845b06f1a196

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
namespace Reaches
theorem _root_.solution {M : Stepped α β} {S t : ℕ} {b : β} {s : M.σ} (h : M.Reaches S b s t) :
    (∀ T, t ≤ T → M.out (M.next^[T] s) = some b) ∧ ∀ n, size (M.next^[n] s) ≤ S := by
  induction h with
  | halt ho hs => exact ⟨fun T _ => by rw [next_iterate_of_out ho, ho], fun n => by rwa [next_iterate_of_out ho]⟩
  | @step s t ho hs _ ih =>
    have e : M.next s = M.step s := by rw [next, ho]
    refine ⟨fun T hT => ?_, fun n => ?_⟩
    · obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
      rw [Function.iterate_succ_apply, e]
      exact ih.1 T' (by omega)
    · cases n with
      | zero => exact hs
      | succ n => rw [Function.iterate_succ_apply, e]; exact ih.2 n
end Reaches
end Groundwork.Stepped
