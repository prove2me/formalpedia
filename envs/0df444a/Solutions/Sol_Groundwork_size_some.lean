-- Prove2me | solution 1 for Groundwork.size_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:20:15.76277+00:00
-- url     : https://prove2.me/submissions/9261e81a-764b-4df3-b317-2e877b6a81ba

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
theorem _root_.solution [HasSize α] (a : α) : size (some a) = size a + 1 := rfl
end Groundwork
