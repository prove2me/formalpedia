-- Prove2me | solution 1 for Groundwork.two_le_len_list
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:03:04.552582+00:00
-- url     : https://prove2.me/submissions/d006483d-6d82-4d32-9b14-be64b8bf88d9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Enc
import Definitions.Def_ToTuring_EncLemmas
import Theorems.Thm_Groundwork_len_list

set_option autoImplicit false
section
section
open Groundwork
open TM Enc
variable {α β : Type} [Enc α] [Enc β]
namespace Groundwork
theorem _root_.solution (l : List α) : 2 ≤ len l := by
  rw [len_list]; omega
end Groundwork
