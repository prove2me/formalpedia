-- Prove2me | solution 1 for Groundwork.SatNet.good_toState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:08:36.83205+00:00
-- url     : https://prove2.me/submissions/11b7a7ee-aa63-426f-866b-3dc7d9a36a8a

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

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}
variable [DecidableEq V]
variable {φ : List (List (V × Bool))} {g μ k : ℕ}
omit [DecidableEq V]
namespace Groundwork.SatNet
theorem _root_.solution (hk : ∀ C ∈ φ, C.length ≤ k) {a : V → Bool} (ha : IsModel φ a) :
    Good φ (toState φ (g := g) (μ := μ) (k := k) a) := by
  refine ⟨fun p hp => by simp [toState, hp], fun c d hlt => ?_, fun p q h => ?_⟩
  · obtain ⟨l, hl, hal⟩ := ha.1 _ (List.getElem_mem hlt)
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
    refine ⟨⟨j, lt_of_lt_of_le hj (hk _ (List.getElem_mem hlt))⟩, ?_⟩
    simp [toState, lit, hlt, hj, hal]
  · obtain ⟨_, h2, h3, _⟩ := h
    unfold lab at h2 h3
    cases hp : lit φ p <;> cases hq : lit φ q <;> simp_all [toState]
end Groundwork.SatNet
