-- Prove2me | solution 1 for Groundwork.Colouring.exists_colouring_fintype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:59:14.371453+00:00
-- url     : https://prove2.me/submissions/8212f04b-760b-4576-9945-d8955bcc5516

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
import Theorems.Thm_Groundwork_Colouring_Zs_eq
import Theorems.Thm_Groundwork_Colouring_exists_colouring_core

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
theorem _root_.solution (hK : 2 ≤ K) (hg : 3 * K ^ 8 ≤ g)
    (hs : ∀ a b, c a b = c b a) (P : ℕ) (hP : ∀ a, ∑ b with b ≠ a, c a b ≤ P) :
    ∃ χ : ι → κ, (∀ γ, K * #{a | χ a = γ} < 2 * g) ∧
      ∀ γ γ', γ ≠ γ' → K ^ 3 * ∑ a with χ a = γ, ∑ b with χ b = γ', c a b
        ≤ K * (∑ a, ∑ b with b ≠ a, c a b) + g * P := by
  have hg' : 4 * K ^ 6 + K ^ 2 < g := by
    have h4 : 4 ≤ K ^ 2 := by nlinarith
    have h6 : 4 * K ^ 6 ≤ K ^ 8 := by
      calc 4 * K ^ 6 ≤ K ^ 2 * K ^ 6 := Nat.mul_le_mul_right _ h4
        _ = K ^ 8 := by ring
    have h2 : K ^ 2 ≤ K ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    have h0 : 0 < K ^ 8 := pow_pos (by omega) 8
    omega
  obtain ⟨χ, h1, h2⟩ := exists_colouring_core (κ := κ) (fun a b => if b ≠ a then c a b else 0)
    (by simp) (fun a b => by simp only [hs a b, ne_comm]) P
    (fun a => by rw [← sum_filter]; exact hP a) (by omega) hg'
  refine ⟨χ, fun γ => by rw [← Zs_eq]; exact h1 γ, fun γ γ' hne => ?_⟩
  have hU : Us (fun a b => if b ≠ a then c a b else 0) = ∑ a, ∑ b with b ≠ a, c a b := by
    unfold Us
    rw [Fintype.sum_prod_type]
    exact sum_congr rfl fun a _ => (sum_filter _ _).symm
  have hY : Ys (fun a b => if b ≠ a then c a b else 0) γ γ' χ
      = ∑ a with χ a = γ, ∑ b with χ b = γ', c a b := by
    unfold Ys
    rw [Fintype.sum_prod_type, sum_filter]
    refine sum_congr rfl fun a _ => ?_
    by_cases ha : χ a = γ
    · rw [if_pos ha, sum_filter]
      refine sum_congr rfl fun b _ => ?_
      by_cases hb : χ b = γ'
      · have hba : b ≠ a := by
          rintro rfl
          exact hne (ha.symm.trans hb)
        simp [ha, hb, hba]
      · simp [hb]
    · simp [ha]
  have := h2 γ γ'
  rwa [hU, hY] at this
end Groundwork.Colouring
