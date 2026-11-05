-- Prove2me | solution 1 for Groundwork.size_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:19:57.458338+00:00
-- url     : https://prove2.me/submissions/1f179236-4e3c-4337-89d0-83935a7af806

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
theorem _root_.solution [HasSize α] [HasSize β] (b : β) : size (Sum.inr b : α ⊕ β) = size b + 1 := rfl
end Groundwork
