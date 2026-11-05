-- Prove2me | solution 1 for Groundwork.Stepped.branch_runs_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:54:48.904377+00:00
-- url     : https://prove2.me/submissions/ddcb3ff0-af4b-422d-8720-883e3e06bdd4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Comb
import Theorems.Thm_Groundwork_Stepped_branch_reaches_inr

set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
variable {α α₁ α₂ β γ δ ι : Type}
namespace Groundwork.Stepped
theorem _root_.solution {sel : α → α₁ ⊕ α₂} {M₁ : Stepped α₁ β} {M₂ : Stepped α₂ β} {a : α} {y : α₂}
    {S t : ℕ} {b : β} (hs : sel a = .inr y) (h : M₂.Runs y t S b) : (branch sel M₁ M₂).Runs a t (S + 1) b := by
  have e : (branch sel M₁ M₂).init a = .inr (M₂.init y) := by
    change (match sel a with | .inl x => _ | .inr y => _) = _
    rw [hs]
  unfold Runs
  rw [e]
  exact branch_reaches_inr h
end Groundwork.Stepped
