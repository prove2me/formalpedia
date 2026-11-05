-- Prove2me | solution 1 for Groundwork.RebalanceArith.beta_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:06:12.079934+00:00
-- url     : https://prove2.me/submissions/d690224a-5a98-4a15-a83e-151e6a84f44c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_StepMachines_Math_RebalanceArith

set_option autoImplicit false
section
open Groundwork Groundwork.RebalanceArith
namespace Groundwork.RebalanceArith
theorem _root_.solution {K g P U β : ℕ} (hK : 1 ≤ K) (hg : 1 ≤ g) (hP : 1 ≤ P) (hU : U ≤ g * P)
    (hβ : K ^ 3 * β ≤ K ^ 3 + K * U + g * P) : β ≤ 3 * (g * P) := by
  have hK3 : 1 ≤ K ^ 3 := Nat.one_le_pow _ _ hK
  have h1 : K * U ≤ K ^ 3 * U := Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) K)
  have h2 : g * P ≤ K ^ 3 * (g * P) := Nat.le_mul_of_pos_left _ hK3
  have h3 : K ^ 3 * β ≤ K ^ 3 * (1 + U + g * P) := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    omega
  have h4 : β ≤ 1 + U + g * P := Nat.le_of_mul_le_mul_left h3 hK3
  have h5 : 1 ≤ g * P := Nat.mul_pos hg hP
  omega
end Groundwork.RebalanceArith
