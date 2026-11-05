-- Prove2me | solution 1 for Groundwork.Grid.rowNet_c_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:08:12.405147+00:00
-- url     : https://prove2.me/submissions/87d7bc96-efb5-4bd8-ab8a-a3ae9c3f57b3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_RowNet
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_Groundwork_Grid_Size
import Theorems.Thm_Groundwork_card_pairs

section
namespace Groundwork.Grid
open Finset
private theorem sum_le_card_mul {ι : Type} (s : Finset ι) (f : ι → ℕ) (c : ℕ) (h : ∀ i ∈ s, f i ≤ c) :
    ∑ i ∈ s, f i ≤ #s * c :=
  (Finset.sum_le_sum h).trans (Finset.sum_const_nat fun _ _ => rfl).le
private theorem two_mul_pairs (X : Type) [Fintype X] [LinearOrder X] :
    2 * #(pairs X) = Fintype.card X * (Fintype.card X - 1) := by
  rw [card_pairs, Nat.choose_two_right, Nat.mul_div_cancel' (even_iff_two_dvd.1 (Nat.even_mul_pred_self _))]
private theorem cap_bound {g L m : ℕ} (hm : 1 ≤ m) (X : Type) [Fintype X] [LinearOrder X] (hX : Fintype.card X = g)
    (F : X × X → ℕ) (hF : ∀ k, F k ≤ 2 * m * L) :
    g * L + ∑ k : X × X with k.1 < k.2, F k ≤ g ^ 2 * (m * L) := by
  have h1 : ∑ k : X × X with k.1 < k.2, F k ≤ #(pairs X) * (2 * m * L) := sum_le_card_mul _ _ _ fun k _ => hF k
  have h2 := two_mul_pairs X
  rw [hX] at h2
  have h3 : #(pairs X) * (2 * m * L) = g * (g - 1) * (m * L) := by rw [← h2]; ring
  rw [h3] at h1
  have h4 : g * L ≤ g * (m * L) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hm)
  refine (Nat.add_le_add h4 h1).trans (le_of_eq ?_)
  clear h1 h2 h3 h4 hX
  rcases g with _ | n
  · simp
  · simp only [Nat.add_sub_cancel]; ring
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
theorem _root_.solution {g L m : ℕ} (hm : 1 ≤ m) (hγ : Fintype.card γ = g) (R : Inst (ρ × γ) α) (C : Rect ρ γ → Cut α τ)
    (t₀ : τ) (hcap : ∀ ω, (C ω).cap ≤ 2 * m * L) (a b : ρ) : (rowNet R C t₀ L).c a b ≤ g ^ 2 * (m * L) := by
  simp only [rowNet, hγ]
  exact cap_bound hm γ hγ _ fun k => hcap _
end Groundwork.Grid
