-- Prove2me | solution 1 for Groundwork.Network.merge_sized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:46:09.310508+00:00
-- url     : https://prove2.me/submissions/f6060805-049c-423d-b40c-87f6b107a1d0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
import Theorems.Thm_Groundwork_abs_prod_le_two_pow
import Theorems.Thm_Groundwork_card_class_pairs_le
import Theorems.Thm_P2M_Groundwork_Network_merge___472728bb004e
import Theorems.Thm_Groundwork_Network_merge_shaped

set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
open Groundwork.Network
namespace Groundwork.Network
theorem _root_.solution [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J'] (N : Network J σ τ) (χ : J → J')
    (s₀ : σ) (t₀ : τ) {P B m : ℕ} (h : N.Sized P B) (hm : ∀ G, #{a | χ a = G} ≤ m) :
    (N.merge χ s₀ t₀).Sized (P * m) (B * (m + m * m)) := by
  have hmono : (2 : ℤ) ^ (B * (m * m)) ≤ 2 ^ (B * (m + m * m)) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (Nat.le_add_left _ _))
  refine ⟨merge_shaped N χ s₀ t₀ h.toShaped hm, ?_, ?_, ?_⟩
  · intro G z
    simp only [merge]
    rw [abs_mul, mul_add, pow_add]
    refine mul_le_mul (abs_prod_le_two_pow _ _ (fun a _ => h.abs_W a _) (hm G)) ?_ (abs_nonneg _)
      (pow_nonneg (by norm_num) _)
    refine abs_prod_le_two_pow _ _ (fun p hp => h.abs_Ψ _ _ _ _ ?_)
      ((Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))).trans (card_class_pairs_le χ hm G G))
    have : p.1 < p.2 := by simpa [pairs] using (Finset.mem_filter.1 hp).1
    exact this.ne
  · intro G G' z t
    simp only [merge]
    exact (abs_prod_le_two_pow _ _ (fun p _ => h.abs_f _ _ _ _) (card_class_pairs_le χ hm G G')).trans hmono
  · intro G G' z z' hne
    rw [merge_Ψ _ _ _ _ hne]
    refine (abs_prod_le_two_pow _ _ (fun p hp => h.abs_Ψ _ _ _ _ ?_) (card_class_pairs_le χ hm G G')).trans hmono
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
    rintro he
    rw [he, h2] at h1
    exact hne h1.symm
end Groundwork.Network
