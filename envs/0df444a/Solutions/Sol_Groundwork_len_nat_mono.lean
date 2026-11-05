-- Prove2me | solution 1 for Groundwork.len_nat_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:44:48.772762+00:00
-- url     : https://prove2.me/submissions/1d00dc34-08a3-49d3-9d0c-87291fc809f0

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
theorem _root_.solution {m n : ℕ} (h : m ≤ n) : len m ≤ len n := by
  rw [len_nat, len_nat]; have := Nat.size_le_size h; omega
end Groundwork
