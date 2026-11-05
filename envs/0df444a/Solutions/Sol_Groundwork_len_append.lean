-- Prove2me | solution 1 for Groundwork.len_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:35:17.5546+00:00
-- url     : https://prove2.me/submissions/0f00320a-2d14-4292-bb55-8024d1ffc8c7

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
theorem _root_.solution (l l' : List α) : len (l ++ l') + 2 = len l + len l' := by
  induction l with
  | nil => rw [List.nil_append, len_nil]; omega
  | cons a l ih => rw [List.cons_append, len_cons, len_cons]; omega
end Groundwork
