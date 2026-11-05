-- Prove2me | solution 1 for Groundwork.Stepped.mapIn_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:43:40.49233+00:00
-- url     : https://prove2.me/submissions/7ce8ad22-780d-4fe1-9704-0b4e4eff8a1f

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
theorem _root_.solution {f : α → β} {M : Stepped β γ} {s : M.σ} {t S : ℕ} {c : γ} (h : M.Reaches S c s t) :
    (mapIn f M).Reaches S c s t := by
  induction h with
  | halt ho hs => exact .halt ho hs
  | step ho hs _ ih => exact .step ho hs ih
end Groundwork.Stepped
