-- Prove2me | solution 1 for Groundwork.PB.mono_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:43:55.149855+00:00
-- url     : https://prove2.me/submissions/8ce2ba3e-1f3e-428c-aba2-7d8c305dfce9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Order.Monotone.Basic
import Definitions.Def_ToTuring_Bound

set_option autoImplicit false
section
section
open Groundwork
open Groundwork.PB
variable {t s : ℕ → ℕ}
namespace Groundwork.PB
theorem _root_.solution (c : ℕ) : PB (fun n => c * (n + 1) ^ c) ∧ Monotone fun n => c * (n + 1) ^ c := by
  exact ⟨⟨c, fun _ => le_rfl⟩, fun _ _ h => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ h) c)⟩
end Groundwork.PB
