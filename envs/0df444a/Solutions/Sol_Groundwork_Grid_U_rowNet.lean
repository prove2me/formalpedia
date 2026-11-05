-- Prove2me | solution 1 for Groundwork.Grid.U_rowNet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:40:22.826702+00:00
-- url     : https://prove2.me/submissions/e08c1c97-e309-400f-a0f2-d79d18dc59e4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_RowNet
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_Groundwork_Grid_Size
import Theorems.Thm_Groundwork_card_pairs
import Theorems.Thm_P2M_Groundwork_Grid___eq_product_67598949e673

section
namespace Groundwork.Grid
open Finset
private theorem two_mul_pairs (X : Type) [Fintype X] [LinearOrder X] :
    2 * #(pairs X) = Fintype.card X * (Fintype.card X - 1) := by
  rw [card_pairs, Nat.choose_two_right, Nat.mul_div_cancel' (even_iff_two_dvd.1 (Nat.even_mul_pred_self _))]
private theorem sum_erase_eq {X : Type} [Fintype X] [LinearOrder X] (h : X × X → ℕ) :
    ∑ a, ∑ b ∈ univ.erase a, h (min a b, max a b) = 2 * ∑ p ∈ pairs X, h p := by
  have h0 : ∀ a b : X, (if b ≠ a then h (min a b, max a b) else 0) =
      (if a < b then h (a, b) else 0) + (if b < a then h (b, a) else 0) := by
    intro a b
    rcases lt_trichotomy a b with hab | hab | hab
    · simp [hab, hab.ne', hab.le, not_lt.2 hab.le]
    · simp [hab]
    · simp [hab, hab.ne, hab.le, not_lt.2 hab.le]
  have h1 : ∑ p ∈ pairs X, h p = ∑ a, ∑ b, if a < b then h (a, b) else 0 := by
    rw [pairs, Finset.sum_filter, Fintype.sum_prod_type]
  have h2 : ∑ a : X, ∑ b : X, (if b < a then h (b, a) else 0) = ∑ a, ∑ b, if a < b then h (a, b) else 0 :=
    Finset.sum_comm
  calc ∑ a, ∑ b ∈ univ.erase a, h (min a b, max a b)
      = ∑ a, ∑ b, if b ≠ a then h (min a b, max a b) else 0 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.filter_ne' univ a, Finset.sum_filter]
    _ = 2 * ∑ p ∈ pairs X, h p := by
        simp only [h0, Finset.sum_add_distrib]
        rw [h2, h1, two_mul]
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [Fintype α] [DecidableEq α]
end Groundwork.Grid
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
namespace Groundwork.Grid
theorem _root_.solution {g L : ℕ} (hρ : Fintype.card ρ = g) (hγ : Fintype.card γ = g) (R : Inst (ρ × γ) α)
    (C : Rect ρ γ → Cut α τ) (t₀ : τ) :
    (rowNet R C t₀ L).U = g ^ 2 * (g - 1) * L + 2 * ∑ ω ∈ Ω ρ γ, (C ω).cap := by
  have hsum : (∑ ω ∈ Ω ρ γ, (C ω).cap) = ∑ p ∈ pairs ρ, ∑ k : γ × γ with k.1 < k.2, (C (p, k)).cap := by
    rw [Ω_eq_product, Finset.sum_product]
  have h := sum_erase_eq (X := ρ) fun p => Fintype.card γ * L + ∑ k : γ × γ with k.1 < k.2, (C (p, k)).cap
  rw [Network.U]
  simp only [rowNet]
  rw [h, Finset.sum_add_distrib, ← hsum, Finset.sum_const, smul_eq_mul, mul_add,
    ← mul_assoc, two_mul_pairs, hρ, hγ]
  ring
end Groundwork.Grid
