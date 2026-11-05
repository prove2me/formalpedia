-- Prove2me | solution 1 for Groundwork.GridArith.four_mul_choose_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:55:29.917257+00:00
-- url     : https://prove2.me/submissions/6fee6c72-445b-4466-9342-453e90b09674

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_StepMachines_Math_GridArith

set_option autoImplicit false
section
section
open Groundwork Groundwork.GridArith
namespace Groundwork.GridArith
theorem _root_.solution (g : ℕ) : 4 * g.choose 2 ^ 2 ≤ g ^ 4 := by
  have h : 2 * g.choose 2 ≤ g ^ 2 := by
    rw [Nat.choose_two_right]
    calc 2 * (g * (g - 1) / 2) ≤ g * (g - 1) := Nat.mul_div_le _ _
      _ ≤ g * g := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = g ^ 2 := (sq g).symm
  calc 4 * g.choose 2 ^ 2 = (2 * g.choose 2) ^ 2 := by ring
    _ ≤ (g ^ 2) ^ 2 := Nat.pow_le_pow_left h 2
    _ = g ^ 4 := by ring
end Groundwork.GridArith
