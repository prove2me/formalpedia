-- Prove2me | solution 1 for Groundwork.len_drop_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:04:12.15442+00:00
-- url     : https://prove2.me/submissions/e77a5d8a-030a-4d4c-8292-e08968a5f387

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Enc
import Definitions.Def_ToTuring_EncLemmas
import Theorems.Thm_Groundwork_len_append
import Theorems.Thm_Groundwork_two_le_len_list

set_option autoImplicit false
section
section
open Groundwork
open TM Enc
variable {α β : Type} [Enc α] [Enc β]
namespace Groundwork
theorem _root_.solution (l : List α) (k : ℕ) : len (l.drop k) ≤ len l := by
  have h := len_append (l.take k) (l.drop k)
  rw [List.take_append_drop] at h
  have := two_le_len_list (l.take k)
  omega
end Groundwork
