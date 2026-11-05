-- Prove2me | solution 1 for Groundwork.card_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:32:30.233464+00:00
-- url     : https://prove2.me/submissions/29647a79-3b70-4155-a394-0332cf60651c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Function
import Definitions.Def_Groundwork_Net_Calculus
namespace Groundwork
open Finset
variable {ι X' τ A α : Type*}
private theorem two_mul_card_pairs' [Fintype α] [LinearOrder α] :
    2 * #(pairs α) + Fintype.card α = Fintype.card α * Fintype.card α := by
  have h1 : #(univ.filter fun p : α × α => p.2 < p.1) = #(pairs α) :=
    Finset.card_nbij' Prod.swap Prod.swap (by intro p; simp [pairs]) (by intro p; simp [pairs]) (by intro p; simp)
      (by intro p; simp)
  have h2 : #(univ.filter fun p : α × α => p.1 = p.2) = Fintype.card α :=
    Finset.card_nbij' Prod.fst (fun a => (a, a)) (by intro p; simp) (by intro p; simp)
      (by rintro ⟨a, b⟩ h; simp at h; simp [h]) (by intro p; simp)
  have h3 : #(univ : Finset (α × α)) = #(pairs α) + #(univ.filter fun p : α × α => p.1 = p.2) +
      #(univ.filter fun p : α × α => p.2 < p.1) := by
    rw [pairs, ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint]
    · congr 1; ext p; simp; exact lt_trichotomy p.1 p.2
    · rw [Finset.disjoint_left]; intro p; simp; grind
    · rw [Finset.disjoint_left]; intro p; simp; grind
  rw [Finset.card_univ, Fintype.card_prod, h1, h2] at h3
  lia
namespace Cross
end Cross
end Groundwork
set_option autoImplicit false
section
open Groundwork
open Finset
variable {ι X' τ A α : Type*}
namespace Groundwork
theorem _root_.solution [Fintype α] [LinearOrder α] : #(pairs α) = (Fintype.card α).choose 2 := by
  have h := two_mul_card_pairs' (α := α)
  rw [Nat.choose_two_right]
  have h2 : Fintype.card α * (Fintype.card α - 1) = 2 * #(pairs α) := by
    rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | h0
    · simp [h0] at h ⊢; lia
    · obtain ⟨n, hn⟩ : ∃ n, Fintype.card α = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h0).symm⟩
      rw [hn] at h ⊢
      simp only [Nat.add_sub_cancel]
      grind
  rw [h2]; simp
end Groundwork
