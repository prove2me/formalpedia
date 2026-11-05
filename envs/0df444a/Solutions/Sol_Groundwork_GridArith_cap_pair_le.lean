-- Prove2me | solution 1 for Groundwork.GridArith.cap_pair_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:05:55.186189+00:00
-- url     : https://prove2.me/submissions/2b0ca22a-acc9-4e0f-9744-b0e6e5ac086f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_StepMachines_Math_GridArith
import Theorems.Thm_Groundwork_GridArith_size_three_pow_le
import Theorems.Thm_Groundwork_GridArith_four_rho

set_option autoImplicit false
section
section
open Groundwork Groundwork.GridArith
namespace Groundwork.GridArith
theorem _root_.solution {n d : ℕ} (h : d ≤ n) :
    ((n + Nat.size (3 ^ (n - d)) + (n + Nat.size (3 ^ d)) : ℕ) : ℝ) ≤ 4 * ρ * n + 2 := by
  have h1 := size_three_pow_le (n - d)
  have h2 := size_three_pow_le d
  rw [Nat.cast_sub h] at h1
  rw [four_rho]
  push_cast
  nlinarith
end Groundwork.GridArith
