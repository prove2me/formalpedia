-- Prove2me | solution 1 for Groundwork.Prog.size_pattern_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:11:34.261092+00:00
-- url     : https://prove2.me/submissions/d2096323-5cd2-4be9-89b9-fbf8c3ce6b5e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Side
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Prog_GridCount
import Definitions.Def_StepMachines_Prog_SidePresents
import Theorems.Thm_Groundwork_GridArith_four_mul_choose_sq_le
import Theorems.Thm_Groundwork_size_nat
attribute [local simp] Groundwork.size_nat



set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped
open Groundwork.Grid (he node c2 sideN sideCap)
namespace Groundwork.Prog
theorem _root_.solution {g n y : ℕ} (hy : y < (n + 1) ^ nRect g) : size y ≤ g ^ 4 * n + 1 := by
  rw [size_nat]
  refine Nat.succ_le_succ (Nat.size_le.2 (hy.trans_le ?_))
  have hR : nRect g ≤ g ^ 4 := by
    have := GridArith.four_mul_choose_sq_le g
    unfold nRect
    omega
  calc (n + 1) ^ nRect g ≤ (2 ^ n) ^ nRect g := Nat.pow_le_pow_left Nat.lt_two_pow_self _
    _ = 2 ^ (n * nRect g) := (Nat.pow_mul 2 n _).symm
    _ ≤ 2 ^ (g ^ 4 * n) := Nat.pow_le_pow_right (by omega) (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hR)
end Groundwork.Prog
