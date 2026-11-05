-- Prove2me | solution 1 for Groundwork.wd_int
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:43:09.390926+00:00
-- url     : https://prove2.me/submissions/26a4336f-f949-4f96-88f7-591bacb58f11

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Enc
import Definitions.Def_ToTuring_EncLemmas

set_option autoImplicit false
section
section
open Groundwork
open TM Enc
variable {α β : Type} [Enc α] [Enc β]
namespace Groundwork
theorem _root_.solution (z : ℤ) : wd z = wd (decide (z < 0), z.natAbs) := rfl
end Groundwork
