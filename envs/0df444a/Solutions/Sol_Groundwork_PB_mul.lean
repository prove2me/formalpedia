-- Prove2me | solution 1 for Groundwork.PB.mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:39:13.024062+00:00
-- url     : https://prove2.me/submissions/b500eaf5-f796-4d50-a8e3-8cb4f92ef8a0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Order.Monotone.Basic
import Definitions.Def_ToTuring_Bound
import Theorems.Thm_Groundwork_PB_bound_le

set_option autoImplicit false
section
section
open Groundwork
open Groundwork.PB
variable {t s : ℕ → ℕ}
namespace Groundwork.PB
theorem _root_.solution (ht : PB t) (hs : PB s) : PB fun n => t n * s n := by
  obtain ⟨c, hc⟩ := ht
  obtain ⟨c', hc'⟩ := hs
  refine ⟨c * c' + (c + c'), fun n => ?_⟩
  calc t n * s n ≤ c * (n + 1) ^ c * (c' * (n + 1) ^ c') := Nat.mul_le_mul (hc n) (hc' n)
    _ = c * c' * (n + 1) ^ (c + c') := by rw [pow_add]; ring
    _ ≤ _ := bound_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
end Groundwork.PB
