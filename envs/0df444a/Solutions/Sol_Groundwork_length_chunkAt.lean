-- Prove2me | solution 1 for Groundwork.length_chunkAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:40:20.350486+00:00
-- url     : https://prove2.me/submissions/f289cf82-6aa2-49b8-b606-19491c62a5b2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_CodeMore
import Definitions.Def_StepMachines_Math_CodeSeq

set_option autoImplicit false
section
open Groundwork
open Finset
variable {X : Type*}
namespace Groundwork
theorem _root_.solution (n : ℕ → ℕ) {r κ : ℕ} (hκ : κ < r) {w : List Bool} (hw : w.length = ∑ κ' ∈ range r, n κ') :
    (chunkAt n κ w).length = n κ := by
  have h : ∑ κ' ∈ range (κ + 1), n κ' ≤ ∑ κ' ∈ range r, n κ' :=
    sum_le_sum_of_subset (range_mono hκ)
  rw [sum_range_succ] at h
  rw [chunkAt, List.length_take, List.length_drop, hw]
  omega
end Groundwork
