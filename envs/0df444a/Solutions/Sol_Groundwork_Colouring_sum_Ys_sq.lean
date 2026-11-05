-- Prove2me | solution 1 for Groundwork.Colouring.sum_Ys_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:46:10.53272+00:00
-- url     : https://prove2.me/submissions/5da66785-8f87-4ed3-bdba-81135b6ed0a3

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
import Theorems.Thm_Groundwork_Colouring_card_pairs_le
import Theorems.Thm_Groundwork_Colouring_sum_meet

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
    (hP : ∀ a, ∑ b, c a b ≤ P) (γ γ' : κ) :
    (∑ χ : ι → κ, Ys c γ γ' χ ^ 2) * K ^ 4 ≤ N * Us c ^ 2 + 4 * K ^ 2 * N * P * Us c := by
  have h0 : ∀ χ : ι → κ, Ys c γ γ' χ ^ 2 = ∑ p : ι × ι, ∑ q : ι × ι,
      if (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ') then c p.1 p.2 * c q.1 q.2 else 0 := by
    intro χ
    unfold Ys
    rw [sq, sum_mul_sum]
    refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
    split_ifs <;> simp_all
  simp only [h0]
  rw [sum_comm, sum_mul]
  have h1 : ∀ p : ι × ι, (∑ χ : ι → κ, ∑ q : ι × ι,
      if (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ') then c p.1 p.2 * c q.1 q.2 else 0)
        * K ^ 4 ≤ c p.1 p.2 * (N * Us c + K ^ 2 * N * (4 * P)) := by
    intro p
    rw [sum_comm, sum_mul]
    have h2 : ∀ q : ι × ι, (∑ χ : ι → κ,
        if (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ') then c p.1 p.2 * c q.1 q.2 else 0)
          * K ^ 4 ≤ c p.1 p.2 * (N * c q.1 q.2 + K ^ 2 * N * (c q.1 q.2 * meet p q)) := by
      intro q
      rw [← sum_filter, sum_const, smul_eq_mul]
      by_cases hp : p.1 = p.2
      · rw [hp, hd]; simp
      by_cases hq : q.1 = q.2
      · rw [hq, hd]; simp
      calc #{χ : ι → κ | (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ')}
            * (c p.1 p.2 * c q.1 q.2) * K ^ 4
          = (c p.1 p.2 * c q.1 q.2) *
            (#{χ : ι → κ | (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ')} * K ^ 4) := by ring
        _ ≤ (c p.1 p.2 * c q.1 q.2) * (N + K ^ 2 * N * meet p q) :=
            Nat.mul_le_mul_left _ (card_pairs_le γ γ' p q hp hq)
        _ = c p.1 p.2 * (N * c q.1 q.2 + K ^ 2 * N * (c q.1 q.2 * meet p q)) := by ring
    calc ∑ q : ι × ι, (∑ χ : ι → κ,
        if (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ') then c p.1 p.2 * c q.1 q.2 else 0)
          * K ^ 4
        ≤ ∑ q : ι × ι, c p.1 p.2 * (N * c q.1 q.2 + K ^ 2 * N * (c q.1 q.2 * meet p q)) :=
          sum_le_sum fun q _ => h2 q
      _ = c p.1 p.2 * (N * Us c + K ^ 2 * N * ∑ q : ι × ι, c q.1 q.2 * meet p q) := by
          simp only [← mul_sum, sum_add_distrib, Us]
      _ ≤ c p.1 p.2 * (N * Us c + K ^ 2 * N * (4 * P)) := by
          gcongr
          exact sum_meet c hs P hP p
  calc ∑ p : ι × ι, (∑ χ : ι → κ, ∑ q : ι × ι,
      if (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ') then c p.1 p.2 * c q.1 q.2 else 0)
        * K ^ 4
      ≤ ∑ p : ι × ι, c p.1 p.2 * (N * Us c + K ^ 2 * N * (4 * P)) := sum_le_sum fun p _ => h1 p
    _ = Us c * (N * Us c + K ^ 2 * N * (4 * P)) := by rw [← sum_mul, Us]
    _ = N * Us c ^ 2 + 4 * K ^ 2 * N * P * Us c := by ring
end Groundwork.Colouring
