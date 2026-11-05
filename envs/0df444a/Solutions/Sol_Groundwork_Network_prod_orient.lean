-- Prove2me | solution 1 for Groundwork.Network.prod_orient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:44:25.618956+00:00
-- url     : https://prove2.me/submissions/4fd6ad58-f4c3-48b3-a8bf-61f675255908

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net

set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
open Groundwork.Network
namespace Groundwork.Network
theorem _root_.solution [Fintype J] [LinearOrder J] [LinearOrder J'] (χ : J → J') (F : J × J → ℤ) (hF : ∀ p, F p.swap = F p) :
    ∏ p : J × J with χ p.1 < χ p.2, F p = ∏ p ∈ pairs J with χ p.1 ≠ χ p.2, F p := by
  refine Finset.prod_nbij' (fun p => if p.1 < p.2 then p else p.swap) (fun p => if χ p.1 < χ p.2 then p else p.swap)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    simp only [pairs, mem_filter, mem_univ, true_and] at h ⊢
    split_ifs with hab <;> simp only [Prod.swap_prod_mk] <;> grind
  · rintro ⟨a, b⟩ h
    simp only [pairs, mem_filter, mem_univ, true_and] at h ⊢
    split_ifs with hab <;> simp only [Prod.swap_prod_mk] <;> grind
  · rintro ⟨a, b⟩ h
    simp only [mem_filter, mem_univ, true_and] at h ⊢
    split_ifs <;> simp_all
    grind
  · rintro ⟨a, b⟩ h
    simp only [pairs, mem_filter, mem_univ, true_and] at h ⊢
    split_ifs <;> simp_all
    grind
  · rintro p _
    split_ifs
    · rfl
    · exact (hF p).symm
end Groundwork.Network
