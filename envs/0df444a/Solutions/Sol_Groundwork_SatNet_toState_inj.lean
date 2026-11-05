-- Prove2me | solution 1 for Groundwork.SatNet.toState_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:09:13.8007+00:00
-- url     : https://prove2.me/submissions/87ad0c72-0d56-4298-8b7c-699563d92f94

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
import Theorems.Thm_Groundwork_SatNet_exists_slot

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}
variable [DecidableEq V]
variable {φ : List (List (V × Bool))} {g μ k : ℕ}
namespace Groundwork.SatNet
theorem _root_.solution (hk : ∀ C ∈ φ, C.length ≤ k) (hm : φ.length ≤ g * μ) {a a' : V → Bool}
    (ha : IsModel φ a) (ha' : IsModel φ a')
    (h : toState φ (g := g) (μ := μ) (k := k) a = toState φ a') : a = a' := by
  funext v
  by_cases hv : ∃ C ∈ φ, ∃ l ∈ C, l.1 = v
  · obtain ⟨C, hC, l, hl, rfl⟩ := hv
    obtain ⟨p, hp⟩ := exists_slot (g := g) (μ := μ) hk hm hC hl
    have := congrFun (congrFun h p.1) p.2
    simpa [toState, hp] using this
  · have hv' : ∀ C ∈ φ, ∀ l ∈ C, l.1 ≠ v := fun C hC l hl h => hv ⟨C, hC, l, hl, h⟩
    rw [ha.2 v hv', ha'.2 v hv']
end Groundwork.SatNet
