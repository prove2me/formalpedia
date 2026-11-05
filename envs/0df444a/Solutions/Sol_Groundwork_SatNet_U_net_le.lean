-- Prove2me | solution 1 for Groundwork.SatNet.U_net_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:23:07.667912+00:00
-- url     : https://prove2.me/submissions/450cb2b3-aa06-422c-88c0-7d2d45b3dc52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Definitions.Def_StepMachines_Math_SatNet
import Theorems.Thm_Groundwork_SatNet_card_used_le
import Theorems.Thm_Groundwork_SatNet_sum_card_eq
import Theorems.Thm_Groundwork_SatNet_sum_c_le

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}
variable [DecidableEq V]
variable {φ : List (List (V × Bool))} {g μ k : ℕ}
namespace Groundwork.SatNet
theorem _root_.solution : (net φ g μ k).U ≤ 2 * k * φ.length := by
  unfold Network.U
  calc ∑ a, ∑ b ∈ univ.erase a, (net φ g μ k).c a b ≤ ∑ a, 2 * #{s : Sl μ k | lit φ (a, s) ≠ none} :=
        Finset.sum_le_sum fun a _ => sum_c_le a
    _ = 2 * #{p : Slot g μ k | lit φ p ≠ none} := by
        rw [← Finset.mul_sum, sum_card_eq (fun a s => lit φ (a, s) ≠ none)]
    _ ≤ 2 * k * φ.length := by
        have := card_used_le (φ := φ) (g := g) (μ := μ) (k := k)
        rw [Nat.mul_assoc, Nat.mul_comm k]
        omega
end Groundwork.SatNet
