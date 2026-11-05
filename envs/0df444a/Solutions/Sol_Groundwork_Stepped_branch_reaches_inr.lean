-- Prove2me | solution 1 for Groundwork.Stepped.branch_reaches_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:45:54.192885+00:00
-- url     : https://prove2.me/submissions/478d677e-7397-4cc8-be1f-42067b8993fd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Comb

set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
variable {α α₁ α₂ β γ δ ι : Type}
namespace Groundwork.Stepped
theorem _root_.solution {sel : α → α₁ ⊕ α₂} {M₁ : Stepped α₁ β} {M₂ : Stepped α₂ β} {S t : ℕ} {b : β}
    {s : M₂.σ} (h : M₂.Reaches S b s t) : (branch sel M₁ M₂).Reaches (S + 1) b (.inr s) t := by
  induction h with
  | halt ho hs => exact .halt ho (Nat.succ_le_succ hs)
  | step ho hs _ ih => exact .step ho (Nat.succ_le_succ hs) ih
end Groundwork.Stepped
