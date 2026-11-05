-- Prove2me | solution 1 for Groundwork.TM.st4_t1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:30:01.469455+00:00
-- url     : https://prove2.me/submissions/8cad2fb8-6d0a-4962-9f2a-55f82e5ab0da

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Rename
import Definitions.Def_ToTuring_TM_Stacks
import Definitions.Def_ToTuring_TM_Move

set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable (A B₁ B₂ C W : List Sym)
namespace Groundwork.TM
theorem _root_.solution : st4 A B₁ B₂ C .t1 = B₁ := rfl
end Groundwork.TM
