-- Prove2me | solution 1 for Groundwork.Grid.ixOf_bijOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:08:26.532941+00:00
-- url     : https://prove2.me/submissions/ee1215e5-7923-4e44-b51f-7a5ab14f0cf3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_Digits
import Theorems.Thm_Groundwork_Grid_mixed_inj
import Theorems.Thm_Groundwork_Grid_mixed_lt
import Theorems.Thm_Groundwork_Grid_mixed_surj
import Theorems.Thm_Groundwork_Grid_nRect_eq
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
theorem _root_.solution (g : ℕ) : Set.BijOn (ixOf g) (Ω (Fin g) (Fin g)) (range (nRect g)) := by
  rw [nRect_eq]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨a, b⟩, ⟨i, i'⟩⟩ h
    simp only [Ω, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h
    simp only [coe_range, Set.mem_Iio, ixOf]
    exact mixed_lt (tri_lt (Fin.lt_def.1 h.1) b.2) (tri_lt (Fin.lt_def.1 h.2) i'.2)
  · rintro ⟨⟨a, b⟩, ⟨i, i'⟩⟩ h ⟨⟨a₂, b₂⟩, ⟨i₂, i₂'⟩⟩ h₂ heq
    simp only [Ω, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h h₂
    simp only [ixOf] at heq
    obtain ⟨e1, e2⟩ := mixed_inj (n := c2 g) (tri_lt (Fin.lt_def.1 h.2) i'.2) (tri_lt (Fin.lt_def.1 h₂.2) i₂'.2) heq
    obtain ⟨e3, e4⟩ := tri_inj (Fin.lt_def.1 h.1) (Fin.lt_def.1 h₂.1) e1
    obtain ⟨e5, e6⟩ := tri_inj (Fin.lt_def.1 h.2) (Fin.lt_def.1 h₂.2) e2
    rw [Fin.ext e3, Fin.ext e4, Fin.ext e5, Fin.ext e6]
  · intro z hz
    simp only [coe_range, Set.mem_Iio] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mixed_surj hz
    obtain ⟨a, b, hab, hb, rfl⟩ := tri_surj (K := g) hx
    obtain ⟨i, i', hii, hi', rfl⟩ := tri_surj (K := g) hy
    refine ⟨((⟨a, by omega⟩, ⟨b, hb⟩), (⟨i, by omega⟩, ⟨i', hi'⟩)), ?_, rfl⟩
    simp only [Ω, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, Fin.lt_def]
    exact ⟨hab, hii⟩
end Groundwork.Grid
