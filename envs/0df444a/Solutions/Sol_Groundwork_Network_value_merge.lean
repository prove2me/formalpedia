-- Prove2me | solution 1 for Groundwork.Network.value_merge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:46:18.955429+00:00
-- url     : https://prove2.me/submissions/808231c2-263f-4c5e-8e42-0301cc2885de

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
import Theorems.Thm_Groundwork_Network_merge_summand
import Theorems.Thm_Groundwork_mem_tuples


set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
open Groundwork.Network
namespace Groundwork.Network
theorem _root_.solution [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J'] (N : Network J σ τ) (χ : J → J')
    (s₀ : σ) (t₀ : τ) : (N.merge χ s₀ t₀).value = N.value := by
  unfold value
  symm
  refine Finset.sum_nbij' (fun z G a => if χ a = G then z a else s₀) (fun Z a => Z (χ a) a) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rw [Fintype.mem_piFinset] at hz ⊢
    intro G
    exact (mem_tuples _ _ _ _).2 fun a => ⟨fun h => by simp [h, hz a], fun h => by simp [h]⟩
  · intro Z hZ
    rw [Fintype.mem_piFinset] at hZ ⊢
    intro a
    exact ((mem_tuples _ _ _ _).1 (hZ (χ a)) a).1 rfl
  · intro z _
    funext a
    simp
  · intro Z hZ
    rw [Fintype.mem_piFinset] at hZ
    funext G a
    by_cases h : χ a = G
    · subst h; simp
    · simp [h, ((mem_tuples _ _ _ _).1 (hZ G) a).2 h]
  · intro z _
    exact merge_summand N χ s₀ t₀ z
end Groundwork.Network
