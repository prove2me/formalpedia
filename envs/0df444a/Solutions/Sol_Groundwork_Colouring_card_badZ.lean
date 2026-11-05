-- Prove2me | solution 1 for Groundwork.Colouring.card_badZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:44:43.427918+00:00
-- url     : https://prove2.me/submissions/d96133e3-aa3b-477c-8e0c-25cf27ecf992

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
import Theorems.Thm_Groundwork_Colouring_sum_Zs
import Theorems.Thm_Groundwork_Colouring_sum_Zs_sq

set_option autoImplicit false
section
open Finset
open Groundwork Groundwork.Colouring
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
local notation "K" => Fintype.card κ
local notation "g" => Fintype.card ι
local notation "N" => (Fintype.card κ ^ Fintype.card ι)
namespace Groundwork.Colouring
theorem _root_.solution (γ : κ) : #{χ : ι → κ | 2 * g ≤ K * Zs γ χ} * g ≤ K * N := by
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · rw [h0]; simp
  have hc := cheb_nat (fun χ : ι → κ => Zs γ χ) K g (g * K * N) 1 g
    (by rw [sum_Zs]; simp [mul_comm]) (by simpa [mul_comm] using sum_Zs_sq (ι := ι) γ)
  have e : ∀ χ : ι → κ, (1 * g + g ≤ 1 * (K * Zs γ χ)) ↔ (2 * g ≤ K * Zs γ χ) := by
    intro χ; omega
  simp only [e] at hc
  have : (#{χ : ι → κ | 2 * g ≤ K * Zs γ χ} * g) * g ≤ (K * N) * g := by
    calc _ = #{χ : ι → κ | 2 * g ≤ K * Zs γ χ} * g ^ 2 := by ring
      _ ≤ 1 ^ 2 * (g * K * N) := hc
      _ = (K * N) * g := by ring
  exact Nat.le_of_mul_le_mul_right this hpos
end Groundwork.Colouring
