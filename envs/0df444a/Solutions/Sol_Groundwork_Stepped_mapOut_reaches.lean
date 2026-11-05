-- Prove2me | solution 1 for Groundwork.Stepped.mapOut_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:43:41.475575+00:00
-- url     : https://prove2.me/submissions/0fe0276b-f7bf-4867-a6bc-def9fb5331b7

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
theorem _root_.solution {M : Stepped α β} {f : β → γ} {s : M.σ} {t S : ℕ} {b : β} (h : M.Reaches S b s t) :
    (mapOut M f).Reaches S (f b) s t := by
  induction h with
  | halt ho hs => exact .halt (by change (M.out _).map f = _; rw [ho]; rfl) hs
  | step ho hs _ ih => exact .step (by change (M.out _).map f = _; rw [ho]; rfl) hs ih
end Groundwork.Stepped
