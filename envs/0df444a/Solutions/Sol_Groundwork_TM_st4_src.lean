-- Prove2me | solution 1 for Groundwork.TM.st4_src
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:30:16.794084+00:00
-- url     : https://prove2.me/submissions/65cdaa83-1451-4f77-89f7-380e785a1cab

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
theorem _root_.solution : st4 A B₁ B₂ C .src = A := rfl
end Groundwork.TM
