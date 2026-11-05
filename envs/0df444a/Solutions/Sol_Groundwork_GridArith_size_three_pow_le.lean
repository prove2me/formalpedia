-- Prove2me | solution 1 for Groundwork.GridArith.size_three_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:04:41.052396+00:00
-- url     : https://prove2.me/submissions/2393aa90-a140-47be-87b0-647582b67cff

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
theorem _root_.solution (c : ℕ) : ((Nat.size (3 ^ c) : ℕ) : ℝ) ≤ c * Real.logb 2 3 + 1 := by
  have hpos : 0 < Nat.size (3 ^ c) := Nat.size_pos.2 (by positivity)
  obtain ⟨s, hs⟩ : ∃ s, Nat.size (3 ^ c) = s + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have h : 2 ^ s ≤ 3 ^ c := Nat.lt_size.1 (by omega)
  have h' : (2 : ℝ) ^ s ≤ (3 : ℝ) ^ c := by exact_mod_cast h
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h'
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h2
  rw [hs]
  push_cast
  linarith
end Groundwork.GridArith
