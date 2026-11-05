-- Prove2me | solution 1 for Groundwork.SatNet.sum_in_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:18:47.989914+00:00
-- url     : https://prove2.me/submissions/78c7724f-6fc9-484a-84db-c16a924207b2

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
import Theorems.Thm_Groundwork_SatNet_Consec_pred_unique
import Theorems.Thm_Groundwork_SatNet_idx_injective
import Theorems.Thm_Groundwork_SatNet_Link_used_right
import Theorems.Thm_Groundwork_SatNet_sum_card_eq

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}
variable [DecidableEq V]
variable {φ : List (List (V × Bool))} {g μ k : ℕ}
namespace Groundwork.SatNet
theorem _root_.solution (a : Fin g) : ∑ b, #{s : Sl μ k | Out φ b a s} ≤ #{s : Sl μ k | lit φ (a, s) ≠ none} := by
  rw [sum_card_eq]
  refine Finset.card_le_card_of_forall_subsingleton (fun (q : Slot g μ k) s' => Link φ q (a, s')) ?_ ?_
  · intro q hq
    obtain ⟨s', hl⟩ : Out φ q.1 a q.2 := by simpa using hq
    exact ⟨s', by simpa using hl.used_right, hl⟩
  · intro s' _ q hq q' hq'
    exact hq.2.pred_unique idx_injective hq'.2
end Groundwork.SatNet
