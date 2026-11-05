-- Prove2me | solution 1 for Groundwork.Grid.tri_bijOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:04:35.256952+00:00
-- url     : https://prove2.me/submissions/436dbc53-ffd1-49f2-b1fb-00435b6530a5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_Digits
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
import Theorems.Thm_Groundwork_tri_inj
import Theorems.Thm_Groundwork_tri_lt
import Theorems.Thm_Groundwork_tri_surj
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect)
namespace Groundwork.Grid
theorem _root_.solution (g : ℕ) : Set.BijOn (fun k : Fin g × Fin g => tri k.1 k.2) {k | k.1 < k.2} (range (c2 g)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, i'⟩ h
    simp only [Set.mem_ofPred_eq] at h
    simp only [coe_range, Set.mem_Iio]
    exact tri_lt (Fin.lt_def.1 h) i'.2
  · rintro ⟨i, i'⟩ h ⟨i₂, i₂'⟩ h₂ heq
    simp only [Set.mem_ofPred_eq] at h h₂
    obtain ⟨e1, e2⟩ := tri_inj (Fin.lt_def.1 h) (Fin.lt_def.1 h₂) heq
    rw [Fin.ext e1, Fin.ext e2]
  · intro z hz
    simp only [coe_range, Set.mem_Iio] at hz
    obtain ⟨i, i', hii, hi', rfl⟩ := tri_surj (K := g) hz
    exact ⟨(⟨i, by omega⟩, ⟨i', hi'⟩), Fin.lt_def.2 hii, rfl⟩
end Groundwork.Grid
