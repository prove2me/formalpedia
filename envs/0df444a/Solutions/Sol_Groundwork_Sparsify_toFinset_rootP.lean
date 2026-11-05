-- Prove2me | solution 1 for Groundwork.Sparsify.toFinset_rootP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:33:42.8762+00:00
-- url     : https://prove2.me/submissions/b90d346d-ffdd-4be8-b097-96ad2d465de3

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
import Theorems.Thm_Groundwork_Sparsify_redP_eq
import Theorems.Thm_Groundwork_Sparsify_toFinset_canonP
import Theorems.Thm_Groundwork_Sparsify_map_redLL
import Theorems.Thm_Groundwork_Sparsify_toFinset_redL


set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {τ n : ℕ} {ψ s l h : PFml} {p q : ℕ}
namespace Groundwork.Sparsify
theorem _root_.solution (ψ : PFml) : (toF (rootP ψ)).toFinset = red (toF ψ).toFinset := by
  rw [rootP, redP_eq, toF, map_redLL, toFinset_redL]
  congr 1
  ext X
  simp only [List.mem_toFinset, List.mem_map, List.mem_dedup]
  constructor
  · rintro ⟨Y, ⟨C, hC, rfl⟩, rfl⟩
    exact ⟨C, hC, (toFinset_canonP hC).symm⟩
  · rintro ⟨C, hC, rfl⟩
    exact ⟨_, ⟨C, hC, rfl⟩, toFinset_canonP hC⟩
end Groundwork.Sparsify
