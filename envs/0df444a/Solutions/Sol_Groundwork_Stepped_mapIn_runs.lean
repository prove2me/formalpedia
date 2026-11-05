-- Prove2me | solution 1 for Groundwork.Stepped.mapIn_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:44:40.042044+00:00
-- url     : https://prove2.me/submissions/ebf5c8cf-c7f3-4fc0-b00b-f5a0413d3251

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
import Theorems.Thm_Groundwork_Stepped_mapIn_reaches

set_option autoImplicit false
section
open Groundwork
open Groundwork.Stepped
variable {α β γ τ : Type}
namespace Groundwork.Stepped
theorem _root_.solution {f : α → β} {M : Stepped β γ} {a : α} {t S : ℕ} {c : γ} (h : M.Runs (f a) t S c) :
    (mapIn f M).Runs a t S c := mapIn_reaches h
end Groundwork.Stepped
