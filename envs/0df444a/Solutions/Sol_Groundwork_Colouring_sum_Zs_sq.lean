-- Prove2me | solution 1 for Groundwork.Colouring.sum_Zs_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:05:17.742383+00:00
-- url     : https://prove2.me/submissions/54b2e61b-b88f-48bb-85bb-42aa445a10e4

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
import Theorems.Thm_Groundwork_Colouring_card_one
import Theorems.Thm_Groundwork_Colouring_card_two

set_option autoImplicit false
section
open Finset
open Groundwork Groundwork.Colouring
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
local notation "K" => Fintype.card κ
local notation "g" => Fintype.card ι
local notation "N" => (Fintype.card κ ^ Fintype.card ι)
namespace Groundwork.Colouring
theorem _root_.solution (γ : κ) : (∑ χ : ι → κ, Zs γ χ ^ 2) * K ^ 2 ≤ g ^ 2 * N + g * K * N := by
  have h0 : ∀ χ : ι → κ, Zs γ χ ^ 2 = ∑ a : ι, ∑ b : ι, if χ a = γ ∧ χ b = γ then 1 else 0 := by
    intro χ
    unfold Zs
    rw [sq, sum_mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    split_ifs <;> simp_all
  simp only [h0]
  rw [sum_comm, sum_mul]
  have h1 : ∀ a : ι, (∑ χ : ι → κ, ∑ b : ι, if χ a = γ ∧ χ b = γ then 1 else 0) * K ^ 2
      ≤ g * N + K * N := by
    intro a
    rw [sum_comm, sum_mul]
    have h2 : ∀ b : ι, (∑ χ : ι → κ, if χ a = γ ∧ χ b = γ then 1 else 0) * K ^ 2
        ≤ N + if b = a then K * N else 0 := by
      intro b
      by_cases hab : b = a
      · subst hab
        have := card_one (κ := κ) b γ
        simp only [and_self, ite_true]
        have e : (∑ χ : ι → κ, if χ b = γ then 1 else 0) = #{χ : ι → κ | χ b = γ} := by simp
        rw [e]
        calc #{χ : ι → κ | χ b = γ} * K ^ 2 = (#{χ : ι → κ | χ b = γ} * K) * K := by ring
          _ = K * N := by rw [this]; ring
          _ ≤ N + K * N := Nat.le_add_left _ _
      · have := card_two (κ := κ) (Ne.symm hab) γ γ
        have e : (∑ χ : ι → κ, if χ a = γ ∧ χ b = γ then 1 else 0)
            = #{χ : ι → κ | χ a = γ ∧ χ b = γ} := by simp
        rw [e, this]; simp [hab]
    calc ∑ b : ι, (∑ χ : ι → κ, if χ a = γ ∧ χ b = γ then 1 else 0) * K ^ 2
        ≤ ∑ b : ι, (N + if b = a then K * N else 0) := sum_le_sum fun b _ => h2 b
      _ = g * N + K * N := by simp [sum_add_distrib]
  calc ∑ a : ι, (∑ χ : ι → κ, ∑ b : ι, if χ a = γ ∧ χ b = γ then 1 else 0) * K ^ 2
      ≤ ∑ _a : ι, (g * N + K * N) := sum_le_sum fun a _ => h1 a
    _ = g ^ 2 * N + g * K * N := by simp; ring
end Groundwork.Colouring
