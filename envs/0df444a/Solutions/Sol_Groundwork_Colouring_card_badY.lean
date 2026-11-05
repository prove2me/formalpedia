-- Prove2me | solution 1 for Groundwork.Colouring.card_badY
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:47:07.883099+00:00
-- url     : https://prove2.me/submissions/adf97570-abbf-4c64-ac0e-3e2173c3fb56

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
import Theorems.Thm_Groundwork_Colouring_cheb_nat
import Theorems.Thm_Groundwork_Colouring_Ys_le_Us
import Theorems.Thm_Groundwork_Colouring_Us_le
import Theorems.Thm_Groundwork_Colouring_sum_Ys
import Theorems.Thm_Groundwork_Colouring_sum_Ys_sq

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
    #{χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c γ γ' χ} * g ≤ 4 * K ^ 4 * N := by
  have hU := Us_le c P hP
  rcases Nat.eq_zero_or_pos (g * P) with h0 | hpos
  · have hU0 : Us c = 0 := by omega
    have : ({χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c γ γ' χ} : Finset (ι → κ)) = ∅ := by
      refine filter_false_of_mem fun χ _ => ?_
      have := Ys_le_Us c γ γ' χ
      have hY : Ys c γ γ' χ = 0 := by omega
      simp [hY]
    rw [this]; simp
  have hc := cheb_nat (fun χ : ι → κ => Ys c γ γ' χ) (K ^ 2) (Us c) (4 * K ^ 2 * N * P * Us c) K
    (g * P) (by rw [sum_Ys c hd]; simp)
    (by
      have := sum_Ys_sq c hd hs P hP γ γ'
      rw [← pow_mul]
      simpa using this)
  have hsub : #{χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c γ γ' χ}
      ≤ #{χ : ι → κ | K * Us c + g * P ≤ K * (K ^ 2 * Ys c γ γ' χ)} := by
    refine card_le_card fun χ h => ?_
    simp only [mem_filter, mem_univ, true_and] at h ⊢
    calc K * Us c + g * P ≤ K ^ 3 * Ys c γ γ' χ := h.le
      _ = K * (K ^ 2 * Ys c γ γ' χ) := by ring
  have hPpos : 0 < P := Nat.pos_of_mul_pos_left hpos
  have : (#{χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c γ γ' χ} * g) * (g * P * P)
      ≤ (4 * K ^ 4 * N) * (g * P * P) := by
    calc _ = #{χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c γ γ' χ} * (g * P) ^ 2 := by ring
      _ ≤ #{χ : ι → κ | K * Us c + g * P ≤ K * (K ^ 2 * Ys c γ γ' χ)} * (g * P) ^ 2 :=
          Nat.mul_le_mul_right _ hsub
      _ ≤ K ^ 2 * (4 * K ^ 2 * N * P * Us c) := hc
      _ = (4 * K ^ 4 * N * P) * Us c := by ring
      _ ≤ (4 * K ^ 4 * N * P) * (g * P) := Nat.mul_le_mul_left _ hU
      _ = (4 * K ^ 4 * N) * (g * P * P) := by ring
  exact Nat.le_of_mul_le_mul_right this (Nat.mul_pos hpos hPpos)
end Groundwork.Colouring
