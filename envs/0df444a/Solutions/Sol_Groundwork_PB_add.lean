-- Prove2me | solution 1 for Groundwork.PB.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:39:11.716299+00:00
-- url     : https://prove2.me/submissions/aeae8ca7-4d47-4328-b14c-2ccf22bda707

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
theorem _root_.solution (ht : PB t) (hs : PB s) : PB fun n => t n + s n := by
  obtain ⟨c, hc⟩ := ht
  obtain ⟨c', hc'⟩ := hs
  refine ⟨c + c', fun n => ?_⟩
  rw [Nat.add_mul]
  exact Nat.add_le_add ((hc n).trans (bound_le le_rfl (Nat.le_add_right _ _)))
    ((hc' n).trans (bound_le le_rfl (Nat.le_add_left _ _)))
end Groundwork.PB
