-- Prove2me | solution 1 for Groundwork.SatNet.sum_c_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:21:39.531228+00:00
-- url     : https://prove2.me/submissions/59c28b1d-83df-4474-a9ec-48b65a2ede63

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
import Theorems.Thm_Groundwork_SatNet_sum_out_le
import Theorems.Thm_Groundwork_SatNet_sum_in_le
import Theorems.Thm_Groundwork_SatNet_c_le

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}
variable [DecidableEq V]
variable {φ : List (List (V × Bool))} {g μ k : ℕ}
namespace Groundwork.SatNet
theorem _root_.solution (a : Fin g) :
    ∑ b ∈ univ.erase a, (net φ g μ k).c a b ≤ 2 * #{s : Sl μ k | lit φ (a, s) ≠ none} := by
  calc ∑ b ∈ univ.erase a, (net φ g μ k).c a b ≤ ∑ b, (net φ g μ k).c a b :=
        Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
    _ ≤ ∑ b, (#{s : Sl μ k | Out φ a b s} + #{s : Sl μ k | Out φ b a s}) := Finset.sum_le_sum fun b _ => c_le a b
    _ = ∑ b, #{s : Sl μ k | Out φ a b s} + ∑ b, #{s : Sl μ k | Out φ b a s} := Finset.sum_add_distrib
    _ ≤ 2 * #{s : Sl μ k | lit φ (a, s) ≠ none} := by have := sum_out_le (φ := φ) (μ := μ) (k := k) a
                                                      have := sum_in_le (φ := φ) (μ := μ) (k := k) a
                                                      omega
end Groundwork.SatNet
