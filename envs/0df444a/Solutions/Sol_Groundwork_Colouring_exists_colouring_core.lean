-- Prove2me | solution 1 for Groundwork.Colouring.exists_colouring_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:48:13.028608+00:00
-- url     : https://prove2.me/submissions/83e0384c-5d32-40d9-9664-e6d9149fa3dc

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
import Theorems.Thm_Groundwork_Colouring_card_badZ
import Theorems.Thm_Groundwork_Colouring_card_badY

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
theorem _root_.solution (hd : ∀ a, c a a = 0) (hs : ∀ a b, c a b = c b a) (P : ℕ)
    (hP : ∀ a, ∑ b, c a b ≤ P) (hK : 0 < K) (hg : 4 * K ^ 6 + K ^ 2 < g) :
    ∃ χ : ι → κ, (∀ γ, K * Zs γ χ < 2 * g) ∧
      ∀ γ γ', K ^ 3 * Ys c γ γ' χ ≤ K * Us c + g * P := by
  by_contra hcon
  push Not at hcon
  have hcov : (univ : Finset (ι → κ)) ⊆
      (univ.biUnion fun γ : κ => {χ : ι → κ | 2 * g ≤ K * Zs γ χ}) ∪
      (univ.biUnion fun p : κ × κ => {χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c p.1 p.2 χ}) := by
    intro χ _
    simp only [mem_union, mem_biUnion, mem_univ, mem_filter, true_and, Prod.exists]
    by_cases h : ∀ γ, K * Zs γ χ < 2 * g
    · right; exact hcon χ h
    · left; push Not at h; exact h
  have h1 := card_le_card hcov
  have h2 := card_union_le
      (univ.biUnion fun γ : κ => ({χ : ι → κ | 2 * g ≤ K * Zs γ χ} : Finset (ι → κ)))
      (univ.biUnion fun p : κ × κ =>
        ({χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c p.1 p.2 χ} : Finset (ι → κ)))
  have h3 : #(univ.biUnion fun γ : κ => ({χ : ι → κ | 2 * g ≤ K * Zs γ χ} : Finset (ι → κ))) * g
      ≤ K * (K * N) := by
    calc _ ≤ (∑ γ : κ, #{χ : ι → κ | 2 * g ≤ K * Zs γ χ}) * g :=
          Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ γ : κ, #{χ : ι → κ | 2 * g ≤ K * Zs γ χ} * g := sum_mul _ _ _
      _ ≤ ∑ _γ : κ, K * N := sum_le_sum fun γ _ => card_badZ γ
      _ = K * (K * N) := by simp
  have h4 : #(univ.biUnion fun p : κ × κ =>
        ({χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c p.1 p.2 χ} : Finset (ι → κ))) * g
      ≤ (K * K) * (4 * K ^ 4 * N) := by
    calc _ ≤ (∑ p : κ × κ, #{χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c p.1 p.2 χ}) * g :=
          Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ p : κ × κ, #{χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c p.1 p.2 χ} * g :=
          sum_mul _ _ _
      _ ≤ ∑ _p : κ × κ, 4 * K ^ 4 * N := sum_le_sum fun p _ => card_badY c hd hs P hP p.1 p.2
      _ = (K * K) * (4 * K ^ 4 * N) := by simp
  have h5 : #(univ : Finset (ι → κ)) = N := by simp
  rw [h5] at h1
  have h6 : N * g ≤ (4 * K ^ 6 + K ^ 2) * N := by
    calc N * g ≤ (_ + _) * g := Nat.mul_le_mul_right _ (h1.trans h2)
      _ = _ * g + _ * g := add_mul _ _ _
      _ ≤ K * (K * N) + (K * K) * (4 * K ^ 4 * N) := Nat.add_le_add h3 h4
      _ = (4 * K ^ 6 + K ^ 2) * N := by ring
  have hN : 0 < N := pow_pos hK g
  have : N * g ≤ N * (4 * K ^ 6 + K ^ 2) := by rw [mul_comm N (4 * K ^ 6 + K ^ 2)]; exact h6
  exact absurd (Nat.le_of_mul_le_mul_left this hN) (not_le.2 hg)
end Groundwork.Colouring
