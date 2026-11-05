-- Prove2me | solution 1 for Groundwork.size_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:19:50.979333+00:00
-- url     : https://prove2.me/submissions/b5472fee-2223-4590-a057-c7799abde78a

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
theorem _root_.solution [HasSize α] [HasSize β] (p : α × β) : size p = size p.1 + size p.2 := rfl
end Groundwork
