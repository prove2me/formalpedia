-- Prove2me | solution 1 for Groundwork.Stepped.mapOut_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:44:25.094909+00:00
-- url     : https://prove2.me/submissions/1a5d5952-c739-4648-8c6f-83c24b80396e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
import Theorems.Thm_Groundwork_Stepped_mapOut_reaches

set_option autoImplicit false
section
open Groundwork
open Groundwork.Stepped
variable {α β γ τ : Type}
namespace Groundwork.Stepped
theorem _root_.solution {M : Stepped α β} {f : β → γ} {a : α} {t S : ℕ} {b : β} (h : M.Runs a t S b) :
    (mapOut M f).Runs a t S (f b) := mapOut_reaches h
end Groundwork.Stepped
