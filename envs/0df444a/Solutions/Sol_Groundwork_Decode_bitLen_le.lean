-- Prove2me | solution 1 for Groundwork.Decode.bitLen_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:39:45.000909+00:00
-- url     : https://prove2.me/submissions/f07f1e69-ca56-4524-bce2-5abb00309618

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Data.Nat.Size
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Prog_Decode
import Theorems.Thm_Groundwork_Decode_width_eq

set_option autoImplicit false
section
open Groundwork Groundwork.Decode
open Sat3
namespace Groundwork.Decode
theorem _root_.solution (n : ℕ) : (Nat.log2 (2 * n) + 1) ≤ n + 1 := by
  rw [← width_eq, width]
  split_ifs with h
  · omega
  · refine Nat.size_le.2 ?_
    rw [pow_succ, Nat.mul_comm]
    exact Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (by norm_num)
end Groundwork.Decode
