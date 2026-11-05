-- Prove2me | solution 1 for Groundwork.Colouring.card_pairs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:44:54.314202+00:00
-- url     : https://prove2.me/submissions/8794db78-4148-4eae-97d6-229e2b17e54f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Floor.Semifield
import Definitions.Def_Groundwork_Net_Colouring
import Theorems.Thm_Groundwork_Colouring_card_two
import Theorems.Thm_Groundwork_Colouring_card_four

set_option autoImplicit false
section
open Finset
open Groundwork Groundwork.Colouring
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
local notation "K" => Fintype.card κ
local notation "g" => Fintype.card ι
local notation "N" => (Fintype.card κ ^ Fintype.card ι)
variable (c : ι → ι → ℕ)
namespace Groundwork.Colouring
theorem _root_.solution (γ γ' : κ) (p q : ι × ι) (hp : p.1 ≠ p.2) (hq : q.1 ≠ q.2) :
    #{χ : ι → κ | (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ')} * K ^ 4
      ≤ N + K ^ 2 * N * meet p q := by
  rcases Nat.eq_zero_or_pos (meet p q) with hm | hm
  · rw [hm]
    simp only [meet, Nat.add_eq_zero_iff, ite_eq_right_iff, one_ne_zero, imp_false] at hm
    obtain ⟨⟨⟨m1, m2⟩, m3⟩, m4⟩ := hm
    rw [card_four hp (Ne.symm m1) (Ne.symm m3) (Ne.symm m2) (Ne.symm m4) hq γ γ']
    simp
  · have hle : #{χ : ι → κ | (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ')}
        ≤ #{χ : ι → κ | χ p.1 = γ ∧ χ p.2 = γ'} := by
      refine card_le_card fun χ h => ?_
      simp only [mem_filter, mem_univ, true_and] at h ⊢
      exact h.1
    calc #{χ : ι → κ | (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ')} * K ^ 4
        ≤ #{χ : ι → κ | χ p.1 = γ ∧ χ p.2 = γ'} * K ^ 4 := Nat.mul_le_mul_right _ hle
      _ = K ^ 2 * (#{χ : ι → κ | χ p.1 = γ ∧ χ p.2 = γ'} * K ^ 2) := by ring
      _ = K ^ 2 * N * 1 := by rw [card_two hp γ γ']; ring
      _ ≤ K ^ 2 * N * meet p q := Nat.mul_le_mul_left _ hm
      _ ≤ N + K ^ 2 * N * meet p q := Nat.le_add_left _ _
end Groundwork.Colouring
