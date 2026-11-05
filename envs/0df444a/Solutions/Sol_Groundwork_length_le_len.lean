-- Prove2me | solution 1 for Groundwork.length_le_len
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:27:23.888919+00:00
-- url     : https://prove2.me/submissions/61d5bdb0-3017-404f-83ce-2b5082a681f6

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
theorem _root_.solution (l : List α) : l.length ≤ len l := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih => rw [len_cons, List.length_cons]; omega
end Groundwork
