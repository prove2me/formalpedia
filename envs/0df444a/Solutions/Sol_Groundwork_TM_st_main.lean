-- Prove2me | solution 1 for Groundwork.TM.st_main
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:25:48.771797+00:00
-- url     : https://prove2.me/submissions/b8499cc4-3d33-40a0-9276-e38a21a04433

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Frag
import Definitions.Def_ToTuring_TM_Tree
import Definitions.Def_ToTuring_TM_Stacks

set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable (M A B N W : List Sym)
namespace Groundwork.TM
theorem _root_.solution : st M A B N .main = M := rfl
end Groundwork.TM
