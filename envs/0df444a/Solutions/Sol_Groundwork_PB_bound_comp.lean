-- Prove2me | solution 1 for Groundwork.PB.bound_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:42:39.494256+00:00
-- url     : https://prove2.me/submissions/43817604-4d1a-4d55-a7ad-804cffd432a0

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
theorem _root_.solution (c c' n : ℕ) : c * (c' * (n + 1) ^ c' + 1) ^ c ≤ (c * (c' + 1) ^ c) * (n + 1) ^ (c' * c) := by
  have h1 : 1 ≤ (n + 1) ^ c' := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have h2 : c' * (n + 1) ^ c' + 1 ≤ (c' + 1) * (n + 1) ^ c' := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left h1 _
  calc c * (c' * (n + 1) ^ c' + 1) ^ c ≤ c * ((c' + 1) * (n + 1) ^ c') ^ c :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 c)
    _ = (c * (c' + 1) ^ c) * (n + 1) ^ (c' * c) := by rw [Nat.mul_pow, ← pow_mul, Nat.mul_assoc]
end Groundwork.PB
