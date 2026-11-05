-- Prove2me | solution 1 for Groundwork.Sparsify.nodeP_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:35:58.015126+00:00
-- url     : https://prove2.me/submissions/abba85b1-3fdf-4dcf-9ee2-852a7e98adaf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SparsifyList
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Nodup
import Definitions.Def_StepMachines_Math_SparsifyProg
import Theorems.Thm_Groundwork_Sparsify_toFinset_canonP
import Theorems.Thm_Groundwork_Sparsify_toFinset_rootP
import Theorems.Thm_Groundwork_Sparsify_node_root


set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {τ n : ℕ} {ψ s l h : PFml} {p q : ℕ}
namespace Groundwork.Sparsify
theorem _root_.solution (τ : ℕ) (ψ : PFml) : NodeP τ ψ (rootP ψ) 0 0 := by
  have hmem : ∀ X ∈ rootP ψ, ∃ C ∈ ψ, X = canonP (litsOf ψ) C := by
    intro X hX
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 (List.mem_filter.1 hX).1)
    exact ⟨C, hC, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro X hX
    obtain ⟨C, -, rfl⟩ := hmem X hX
    exact (List.nodup_dedup _).filter _
  · refine List.Nodup.map_on ?_ ((List.nodup_dedup _).filter _)
    intro X hX Y hY hXY
    obtain ⟨C, hC, rfl⟩ := hmem X hX
    obtain ⟨D, hD, rfl⟩ := hmem Y hY
    rw [toFinset_canonP hC, toFinset_canonP hD] at hXY
    apply List.filter_congr
    intro a _
    have := Finset.ext_iff.1 hXY a
    simp only [List.mem_toFinset] at this
    simp only [List.elem_eq_mem, this]
  · rw [toFinset_rootP]
    exact node_root τ _
end Groundwork.Sparsify
