-- Prove2me | solution 1 for Groundwork.Network.merge_summand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:45:34.056193+00:00
-- url     : https://prove2.me/submissions/046b8abd-aa16-4668-8f3d-880e26a27a91

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
import Theorems.Thm_P2M_Groundwork_Network___comm_f75ed8fe8218
import Theorems.Thm_P2M_Groundwork_Network_merge___lt_75b913e72a8f
import Theorems.Thm_Groundwork_Network_prod_orient

set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
open Groundwork.Network
namespace Groundwork.Network
theorem _root_.solution [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J'] (N : Network J σ τ) (χ : J → J')
    (s₀ : σ) (t₀ : τ) (z : J → σ) :
    (∏ a, N.W a (z a)) * ∏ p ∈ pairs J, N.Ψ p.1 p.2 (z p.1) (z p.2) =
    (∏ G, (N.merge χ s₀ t₀).W G (fun a => if χ a = G then z a else s₀)) *
      ∏ q ∈ pairs J', (N.merge χ s₀ t₀).Ψ q.1 q.2 (fun a => if χ a = q.1 then z a else s₀)
        (fun a => if χ a = q.2 then z a else s₀) := by
  set F : J × J → ℤ := fun p => N.Ψ p.1 p.2 (z p.1) (z p.2) with hFdef
  have hW : ∀ G, (N.merge χ s₀ t₀).W G (fun a => if χ a = G then z a else s₀) =
      (∏ a with χ a = G, N.W a (z a)) * ∏ p ∈ pairs J with χ p.1 = G ∧ χ p.2 = G, F p := by
    intro G
    simp only [merge]
    congr 1
    · refine Finset.prod_congr rfl fun a ha => ?_
      simp [(Finset.mem_filter.1 ha).2]
    · refine Finset.prod_congr rfl fun p hp => ?_
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
      simp [F, h1, h2]
  have hΨ : ∀ q ∈ pairs J', (N.merge χ s₀ t₀).Ψ q.1 q.2 (fun a => if χ a = q.1 then z a else s₀)
        (fun a => if χ a = q.2 then z a else s₀) = ∏ p : J × J with χ p.1 = q.1 ∧ χ p.2 = q.2, F p := by
    intro q hq
    have hq' : q.1 < q.2 := by simpa [pairs] using hq
    rw [merge_Ψ_lt N χ s₀ t₀ hq']
    refine Finset.prod_congr rfl fun p hp => ?_
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
    simp [F, h1, h2]
  rw [Finset.prod_congr rfl hΨ]
  simp only [hW, Finset.prod_mul_distrib]
  rw [Finset.prod_fiberwise univ χ (fun a => N.W a (z a))]
  have h1 : ∏ G, ∏ p ∈ pairs J with χ p.1 = G ∧ χ p.2 = G, F p = ∏ p ∈ pairs J with χ p.1 = χ p.2, F p := by
    rw [← Finset.prod_fiberwise ((pairs J).filter fun p => χ p.1 = χ p.2) (fun p => χ p.1)]
    refine Finset.prod_congr rfl fun G _ => ?_
    rw [Finset.filter_filter]
    refine Finset.prod_congr (Finset.filter_congr fun p _ => ?_) fun _ _ => rfl
    grind
  have h2 : ∏ q ∈ pairs J', ∏ p : J × J with χ p.1 = q.1 ∧ χ p.2 = q.2, F p = ∏ p : J × J with χ p.1 < χ p.2, F p := by
    rw [← Finset.prod_fiberwise_of_maps_to (s := univ.filter fun p : J × J => χ p.1 < χ p.2) (t := pairs J')
      (g := fun p => (χ p.1, χ p.2)) (by intro p; simp [pairs])]
    refine Finset.prod_congr rfl fun q hq => ?_
    have hq' : q.1 < q.2 := by simpa [pairs] using hq
    rw [Finset.filter_filter]
    refine Finset.prod_congr (Finset.filter_congr fun p _ => ?_) fun _ _ => rfl
    rw [Prod.ext_iff]
    grind
  rw [h1, h2, prod_orient χ F (fun p => N.Ψ_comm _ _ _ _), mul_assoc, Finset.prod_filter_mul_prod_filter_not]
end Groundwork.Network
