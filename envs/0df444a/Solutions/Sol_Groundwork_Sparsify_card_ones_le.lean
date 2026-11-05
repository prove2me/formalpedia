-- Prove2me | solution 1 for Groundwork.Sparsify.card_ones_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:24:41.840625+00:00
-- url     : https://prove2.me/submissions/2eb57623-0734-4a17-b0fb-46495bcd6bb8

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
import Theorems.Thm_Groundwork_Sparsify_mul_card_le

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {α : Type*} [DecidableEq α]
variable {τ n : ℕ} {φ F : Finset (Finset α)} {p q : ℕ} {U : Finset α}
namespace Groundwork.Sparsify
theorem _root_.solution (hU : ∀ C ∈ F, C ⊆ U) : (ones F).card ≤ U.card := by
  have := mul_card_le U (ones F) 1 1 (fun C hC => hU C (mem_filter.1 hC).1) (fun C hC => (mem_filter.1 hC).2)
    (fun a => ?_)
  · omega
  · rw [card_le_one]
    intro C hC D hD
    obtain ⟨hC, haC⟩ := mem_filter.1 hC
    obtain ⟨hD, haD⟩ := mem_filter.1 hD
    obtain ⟨c, rfl⟩ := card_eq_one.1 (mem_filter.1 hC).2
    obtain ⟨d, rfl⟩ := card_eq_one.1 (mem_filter.1 hD).2
    rw [mem_singleton] at haC haD
    rw [← haC, ← haD]
end Groundwork.Sparsify
