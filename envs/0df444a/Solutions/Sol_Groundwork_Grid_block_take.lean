-- Prove2me | solution 1 for Groundwork.Grid.block_take
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:09:12.135038+00:00
-- url     : https://prove2.me/submissions/8f0acfe6-40f3-4c8f-98e0-8cbd2b4da4e3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_StepMachines_Math_SideX

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {g n : ℕ}
namespace Groundwork.Grid
theorem _root_.solution (m : ℕ) {i r : ℕ} (hi : i < r) (θ : List Bool) : block m i (θ.take (r * m)) = block m i θ := by
  have h : (i + 1) * m ≤ r * m := Nat.mul_le_mul_right _ hi
  rw [Nat.succ_mul] at h
  rw [block, block, List.drop_take, List.take_take, min_eq_left (by omega)]
end Groundwork.Grid
