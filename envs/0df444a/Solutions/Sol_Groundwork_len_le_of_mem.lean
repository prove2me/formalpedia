-- Prove2me | solution 1 for Groundwork.len_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:27:49.05875+00:00
-- url     : https://prove2.me/submissions/5b98e9a3-8e63-4543-9222-cb3434c865f2

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
theorem _root_.solution {a : α} {l : List α} (h : a ∈ l) : len a ≤ len l := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rw [len_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega
end Groundwork
