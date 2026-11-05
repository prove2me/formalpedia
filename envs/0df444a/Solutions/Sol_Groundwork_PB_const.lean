-- Prove2me | solution 1 for Groundwork.PB.const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:22:36.322056+00:00
-- url     : https://prove2.me/submissions/4994cb2e-e002-4269-9f32-7ff5cc39a994

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
theorem _root_.solution (a : ℕ) : PB fun _ => a := by
  exact ⟨a, fun n => Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.succ_pos n))⟩
end Groundwork.PB
