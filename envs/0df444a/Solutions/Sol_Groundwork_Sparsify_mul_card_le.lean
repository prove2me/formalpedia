-- Prove2me | solution 1 for Groundwork.Sparsify.mul_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:41:32.27765+00:00
-- url     : https://prove2.me/submissions/7accc663-0a95-4b1c-8506-0857f154ce3a

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
variable {τ n : ℕ} {φ F : Finset (Finset α)} {p q : ℕ} {U : Finset α}
namespace Groundwork.Sparsify
theorem _root_.solution (U : Finset α) (G : Finset (Finset α)) (i d : ℕ) (hU : ∀ C ∈ G, C ⊆ U)
    (hi : ∀ C ∈ G, C.card = i) (hd : ∀ a, (G.filter fun C => a ∈ C).card ≤ d) : i * G.card ≤ U.card * d := by
  have := sum_card_inter_le (s := U) (B := G) (n := d) fun a _ => hd a
  rw [sum_congr rfl fun C hC => by rw [inter_eq_right.2 (hU C hC), hi C hC], sum_const] at this
  simpa [Nat.mul_comm] using this
end Groundwork.Sparsify
