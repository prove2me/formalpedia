-- Prove2me | solution 1 for Groundwork.size_list
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:19:53.075551+00:00
-- url     : https://prove2.me/submissions/b94ecd55-9195-4571-8129-a6bfb75f3edb

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
theorem _root_.solution [HasSize α] (l : List α) :
    size l = (l.map fun x => size x + 1).sum + 1 := rfl
end Groundwork
