-- Prove2me | solution 1 for Groundwork.Network.merge_shaped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:45:16.8949+00:00
-- url     : https://prove2.me/submissions/55c8d46a-ad73-4ca0-8e1f-9c841d9813ce

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
import Theorems.Thm_Groundwork_prod_le_prod_of_nonneg
import Theorems.Thm_Groundwork_Network_lab_comm
import Theorems.Thm_Groundwork_Network_card_merge_S
import Theorems.Thm_Groundwork_card_tuples


set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
open Groundwork.Network
namespace Groundwork.Network
theorem _root_.solution [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J'] (N : Network J σ τ) (χ : J → J')
    (s₀ : σ) (t₀ : τ) {P m : ℕ} (h : N.Shaped P) (hm : ∀ G, #{a | χ a = G} ≤ m) :
    (N.merge χ s₀ t₀).Shaped (P * m) := by
  have hc : ∀ G G', (N.merge χ s₀ t₀).c G G' = (N.merge χ s₀ t₀).c G' G := by
    intro G G'
    simp only [merge]
    exact Finset.sum_nbij' Prod.swap Prod.swap (by intro p; simp [and_comm]) (by intro p; simp [and_comm])
      (by intro p; simp) (by intro p; simp) (by intro p _; exact h.c_symm _ _)
  have hlab : ∀ G G', G < G' → #((N.merge χ s₀ t₀).lab G G') ≤ 2 ^ (N.merge χ s₀ t₀).c G G' := by
    intro G G' hlt
    simp only [lab, merge, min_eq_left hlt.le, max_eq_right hlt.le]
    rw [card_tuples, ← Finset.prod_pow_eq_pow_sum]
    refine prod_le_prod_of_nonneg _ _ _ (fun _ _ => Nat.zero_le _) fun p hp => ?_
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
    exact h.card_lab _ _ (by rintro he; rw [he, h2] at h1; exact hlt.ne' h1)
  refine ⟨?_, hc, ?_, ?_⟩
  · intro G
    rw [card_merge_S]
    calc ∏ a with χ a = G, #(N.S a) ≤ ∏ a with χ a = G, 2 ^ P :=
          prod_le_prod_of_nonneg _ _ _ (fun _ _ => Nat.zero_le _) (fun a _ => h.card_S a)
      _ = 2 ^ (P * #{a | χ a = G}) := by rw [Finset.prod_const, pow_mul]
      _ ≤ 2 ^ (P * m) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (hm G))
  · intro G
    simp only [merge]
    calc ∑ G' ∈ univ.erase G, ∑ p : J × J with χ p.1 = G ∧ χ p.2 = G', N.c p.1 p.2
        = ∑ p : J × J with χ p.1 = G ∧ χ p.2 ≠ G, N.c p.1 p.2 := by
          rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter fun p : J × J => χ p.1 = G ∧ χ p.2 ≠ G)
            (t := univ.erase G) (g := fun p => χ p.2) (by intro p; simp)]
          refine Finset.sum_congr rfl fun G' hG' => ?_
          have hne : G' ≠ G := by simpa using hG'
          rw [Finset.filter_filter]
          refine Finset.sum_congr (Finset.filter_congr fun p _ => ?_) fun _ _ => rfl
          grind
      _ ≤ ∑ p : J × J with χ p.1 = G ∧ p.2 ≠ p.1, N.c p.1 p.2 := by
          refine Finset.sum_le_sum_of_subset fun p hp => ?_
          simp only [mem_filter, mem_univ, true_and] at hp ⊢
          grind
      _ = ∑ a with χ a = G, ∑ b ∈ univ.erase a, N.c a b :=
          Finset.sum_finset_product' _ _ _ (by intro p; simp)
      _ ≤ ∑ a with χ a = G, P := Finset.sum_le_sum fun a _ => h.sum_c a
      _ = P * #{a | χ a = G} := by simp [mul_comm]
      _ ≤ P * m := Nat.mul_le_mul_left _ (hm G)
  · intro G G' hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hlab _ _ hlt
    · rw [lab_comm, hc]; exact hlab _ _ hlt
end Groundwork.Network
