-- Prove2me | solution 1 for Groundwork.Stepped.ofFun_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:23:38.203225+00:00
-- url     : https://prove2.me/submissions/97c2edc0-eeec-48fb-b47c-6accf86b9e88

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
theorem _root_.solution [HasSize α] [HasSize β] (f : α → β) (a : α) :
    (ofFun f).Runs a 1 (max (size a) (size (f a)) + 1) (f a) :=
  .step rfl (by change size a + 1 ≤ _; omega) (.halt rfl (by change size (f a) + 1 ≤ _; omega))
end Groundwork.Stepped
