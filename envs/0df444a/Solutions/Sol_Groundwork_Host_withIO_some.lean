-- Prove2me | solution 1 for Groundwork.Host.withIO_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:46:57.025418+00:00
-- url     : https://prove2.me/submissions/5a49262e-5c92-4b5e-b713-10d94202a0b3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Machine_Lift
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Machine_Host

set_option autoImplicit false
section
section
open Groundwork
open TM Turing
open Groundwork.Host
namespace Groundwork.Host
theorem _root_.solution (W : List Bool) (S : Stk → List Sym) (k : Stk) : withIO W S (some k) = S k := rfl
end Groundwork.Host
