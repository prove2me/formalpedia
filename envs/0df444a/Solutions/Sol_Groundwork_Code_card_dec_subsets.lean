-- Prove2me | solution 1 for Groundwork.Code.card_dec_subsets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:07:30.718693+00:00
-- url     : https://prove2.me/submissions/23a0ae8e-e1aa-4642-b916-3112a61a0fd4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Code
import Mathlib.Data.List.GetD
import Definitions.Def_StepMachines_Math_CodeMore
import Theorems.Thm_Groundwork_Code_card_filter_getD

set_option autoImplicit false
section
open Groundwork
open Finset
variable {X Y : Type*}
open Groundwork.Code
variable {S : Finset X} {n : ℕ}
namespace Groundwork.Code
theorem _root_.solution {ι : Type*} [DecidableEq ι] (Ω : Finset ι) (M : ℕ) (idx : ι → ℕ)
    (h : Set.BijOn idx Ω (range M)) {τ : List Bool} (hτ : τ.length = M) :
    #((subsets Ω M idx h).dec τ) = τ.count true := by
  rw [← card_filter_getD, hτ]
  refine card_nbij idx (fun ω hω => ?_) (fun ω hω ω' hω' e => ?_) fun j hj => ?_
  · obtain ⟨h1, h2⟩ := mem_filter.1 hω
    exact mem_filter.2 ⟨h.mapsTo (mem_coe.2 h1), h2⟩
  · exact h.injOn (mem_coe.2 (mem_filter.1 (mem_coe.1 hω)).1) (mem_coe.2 (mem_filter.1 (mem_coe.1 hω')).1) e
  · obtain ⟨h1, h2⟩ := mem_filter.1 (mem_coe.1 hj)
    obtain ⟨ω, hω, rfl⟩ := h.surjOn (mem_coe.2 h1)
    exact ⟨ω, mem_coe.2 (mem_filter.2 ⟨mem_coe.1 hω, h2⟩), rfl⟩
end Groundwork.Code
