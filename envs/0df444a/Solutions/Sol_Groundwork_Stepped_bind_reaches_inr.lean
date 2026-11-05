-- Prove2me | solution 1 for Groundwork.Stepped.bind_reaches_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:43:52.62967+00:00
-- url     : https://prove2.me/submissions/29e72e33-ec6c-4f3e-9ec1-fbdaaa920182

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
theorem _root_.solution [HasSize α] {M : Stepped α β} {N : Stepped (α × β) γ} {S t : ℕ} {c : γ} {s : N.σ}
    (h : N.Reaches S c s t) : (bind M N).Reaches (S + 1) c (.inr s) t := by
  induction h with
  | halt ho hs => exact .halt ho (Nat.succ_le_succ hs)
  | step ho hs _ ih => exact .step ho (Nat.succ_le_succ hs) ih
end Groundwork.Stepped
