-- Prove2me | solution 1 for Groundwork.Sparsify.exists_red_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:24:06.994867+00:00
-- url     : https://prove2.me/submissions/276894e7-1a2c-403d-8e35-19cff03c1ea3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Ring.Nat
import Definitions.Def_StepMachines_Math_Sparsify

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {α : Type*} [DecidableEq α]
namespace Groundwork.Sparsify
theorem _root_.solution {F : Finset (Finset α)} {C : Finset α} (hC : C ∈ F) : ∃ D ∈ red F, D ⊆ C := by
  induction hn : C.card using Nat.strong_induction_on generalizing C with
  | _ n ih =>
    by_cases h : ∀ D ∈ F, D ⊆ C → D = C
    · exact ⟨C, mem_filter.2 ⟨hC, h⟩, Subset.refl _⟩
    · simp only [not_forall] at h
      obtain ⟨D, hD, hDC, hne⟩ := h
      have hlt : D.card < n := hn ▸ card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hDC, hne⟩)
      obtain ⟨E, hE, hED⟩ := ih _ hlt hD rfl
      exact ⟨E, hE, hED.trans hDC⟩
end Groundwork.Sparsify
