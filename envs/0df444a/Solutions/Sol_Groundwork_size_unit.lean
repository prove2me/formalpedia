-- Prove2me | solution 1 for Groundwork.size_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:19:54.977689+00:00
-- url     : https://prove2.me/submissions/e1cdb4c8-49a5-4ddb-98fb-57438bae4586

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped

set_option autoImplicit false
section
open Groundwork
variable {α β : Type}
namespace Groundwork
theorem _root_.solution (u : Unit) : size u = 1 := rfl
end Groundwork
