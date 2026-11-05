-- Prove2me | solution 1 for Groundwork.len_list
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:35:05.07523+00:00
-- url     : https://prove2.me/submissions/2963ef7f-402d-4fae-a3e2-e2729978ec22

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
theorem _root_.solution (l : List α) : len l = (l.map fun a => len a + 2).sum + 2 := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [len_cons, ih, List.map_cons, List.sum_cons]; omega
end Groundwork
