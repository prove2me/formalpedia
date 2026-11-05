-- Prove2me | solution 1 for Groundwork.Prog.Count.sum_words_zip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:20:40.716891+00:00
-- url     : https://prove2.me/submissions/6c09af81-91ed-4fee-8dd5-fdd417a67117

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Theorems.Thm_Groundwork_Prog_Count_boole_congr
import Theorems.Thm_Groundwork_Prog_Count_zip_all_iff
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
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}
namespace Groundwork.Prog.Count
theorem _root_.solution {α : Type} (L : List α) (u v : α → Bool) :
    ∑ θ ∈ words L.length, (if ((L.zip θ).all fun p => u p.1 == p.2) then (1 : ℤ) else 0) *
      (if ((L.zip θ).all fun p => v p.1 == p.2) then 1 else 0) = if (L.all fun p => u p == v p) then 1 else 0 := by
  rw [Finset.sum_eq_single (L.map u)]
  · rw [if_pos ((zip_all_iff u L _ (by simp)).2 rfl), one_mul]
    refine boole_congr ?_
    rw [zip_all_iff v L _ (by simp)]
    simp only [List.all_eq_true, beq_iff_eq, List.map_inj_left]
  · intro θ hθ hne
    rw [if_neg, zero_mul]
    exact fun h => hne ((zip_all_iff u L θ (mem_words.1 hθ)).1 h)
  · intro h
    exact absurd (mem_words.2 (by simp)) h
end Groundwork.Prog.Count
