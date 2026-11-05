-- Prove2me | solution 1 for Groundwork.SatNet.card_used_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:09:40.525402+00:00
-- url     : https://prove2.me/submissions/c2375ab8-988a-4e45-b37e-6130381831ee

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
import Theorems.Thm_Groundwork_SatNet_mul_add_inj

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}
variable [DecidableEq V]
variable {φ : List (List (V × Bool))} {g μ k : ℕ}
omit [DecidableEq V]
namespace Groundwork.SatNet
theorem _root_.solution : #{p : Slot g μ k | lit φ p ≠ none} ≤ φ.length * k := by
  have hc : #(range φ.length ×ˢ range k) = φ.length * k := by simp
  rw [← hc]
  refine Finset.card_le_card_of_injOn (fun p => (p.1.val * μ + p.2.1.val, p.2.2.val)) ?_ ?_
  · intro p hp
    have hp' : lit φ p ≠ none := by simpa using hp
    have hlt : p.1.val * μ + p.2.1.val < φ.length := by
      by_contra h
      exact hp' (by simp [lit, List.getElem?_eq_none (not_lt.1 h)])
    simp [hlt, p.2.2.2]
  · rintro ⟨a, c, j⟩ _ ⟨a', c', j'⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h3, h4⟩ := mul_add_inj c.2 c'.2 h.1
    simp only [Prod.mk.injEq]
    exact ⟨Fin.ext h3, Fin.ext h4, Fin.ext h.2⟩
end Groundwork.SatNet
