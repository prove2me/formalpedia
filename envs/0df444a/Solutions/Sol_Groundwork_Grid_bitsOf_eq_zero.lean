-- Prove2me | solution 1 for Groundwork.Grid.bitsOf_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:06:42.890969+00:00
-- url     : https://prove2.me/submissions/e3df8022-27af-4e62-a33a-f2a9eaa27404

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparse
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_CutWord
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
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (tb capW)
namespace Groundwork.Grid
theorem _root_.solution {n : ℕ} {w : List Bool} (h : w.length = n) :
    bitsOf n w = (fun _ => false) ↔ w.all (!·) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h0 b hb
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hb
    have h1 := congrFun h0 ⟨j, h ▸ hj⟩
    simp only [bitsOf, List.getD_eq_getElem _ _ hj] at h1
    rw [h1]; rfl
  · intro h0
    funext k
    have hk : (k : ℕ) < w.length := h ▸ k.2
    have h1 := h0 _ (List.getElem_mem hk)
    rw [bitsOf, List.getD_eq_getElem _ _ hk]
    simpa using h1
end Groundwork.Grid
