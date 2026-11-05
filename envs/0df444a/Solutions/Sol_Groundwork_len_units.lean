-- Prove2me | solution 1 for Groundwork.len_units
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:27:54.768492+00:00
-- url     : https://prove2.me/submissions/4b2ea164-0a5b-4d26-9a7b-5d6c2a515245

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
theorem _root_.solution (w : List Unit) : len w = 4 * w.length + 2 := by
  induction w with
  | nil => rfl
  | cons u w ih => rw [len_cons, ih, List.length_cons, len_unit]; omega
end Groundwork
