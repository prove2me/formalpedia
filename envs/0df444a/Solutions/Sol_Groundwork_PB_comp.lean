-- Prove2me | solution 1 for Groundwork.PB.comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:43:17.545329+00:00
-- url     : https://prove2.me/submissions/f9f04504-0b8b-4211-b683-fae4c87a5fb7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Order.Monotone.Basic
import Definitions.Def_ToTuring_Bound
import Theorems.Thm_Groundwork_PB_bound_le
import Theorems.Thm_Groundwork_PB_bound_comp

set_option autoImplicit false
section
section
open Groundwork
open Groundwork.PB
variable {t s : ℕ → ℕ}
namespace Groundwork.PB
theorem _root_.solution (ht : PB t) (hs : PB s) : PB fun n => t (s n) := by
  obtain ⟨c, hc⟩ := ht
  obtain ⟨c', hc'⟩ := hs
  refine ⟨c * (c' + 1) ^ c + c' * c, fun n => ?_⟩
  calc t (s n) ≤ c * (s n + 1) ^ c := hc _
    _ ≤ c * (c' * (n + 1) ^ c' + 1) ^ c :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ (hc' n)) c)
    _ ≤ (c * (c' + 1) ^ c) * (n + 1) ^ (c' * c) := bound_comp c c' n
    _ ≤ _ := bound_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
end Groundwork.PB
