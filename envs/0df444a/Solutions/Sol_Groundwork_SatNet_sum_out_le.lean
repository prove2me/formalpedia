-- Prove2me | solution 1 for Groundwork.SatNet.sum_out_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:20:18.541622+00:00
-- url     : https://prove2.me/submissions/6a1914f3-e1de-4378-b1f6-1542abbbb041

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
import Theorems.Thm_Groundwork_SatNet_Consec_succ_unique
import Theorems.Thm_Groundwork_SatNet_idx_injective
import Theorems.Thm_Groundwork_SatNet_Link_used_left
import Theorems.Thm_Groundwork_SatNet_sum_card_eq

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}
variable [DecidableEq V]
variable {φ : List (List (V × Bool))} {g μ k : ℕ}
namespace Groundwork.SatNet
theorem _root_.solution (a : Fin g) : ∑ b, #{s : Sl μ k | Out φ a b s} ≤ #{s : Sl μ k | lit φ (a, s) ≠ none} := by
  rw [sum_card_eq]
  refine Finset.card_le_card_of_injOn (fun q => q.2) ?_ ?_
  · intro q hq
    obtain ⟨s', hl⟩ : Out φ a q.1 q.2 := by simpa using hq
    simpa using hl.used_left
  · rintro ⟨b, s⟩ hq ⟨b', s₁⟩ hq' h
    simp only at h
    subst h
    obtain ⟨s', hl⟩ : Out φ a b s := by simpa using hq
    obtain ⟨s'', hl'⟩ : Out φ a b' s := by simpa using hq'
    have := hl.succ_unique idx_injective hl'
    simp only [Prod.mk.injEq] at this
    simp [this.1]
end Groundwork.SatNet
