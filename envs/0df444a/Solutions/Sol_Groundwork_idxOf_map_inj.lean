-- Prove2me | solution 1 for Groundwork.idxOf_map_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:05:43.095823+00:00
-- url     : https://prove2.me/submissions/431c53e7-9e8f-4e9e-9ad5-ca0128e56047

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
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
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution {ι κ : Type*} [BEq ι] [LawfulBEq ι] [BEq κ] [LawfulBEq κ] {f : ι → κ}
    (hf : Function.Injective f) (e : List ι) (i : ι) : (e.map f).idxOf (f i) = e.idxOf i := by
  induction e with
  | nil => rfl
  | cons j e ih =>
    rw [List.map_cons, List.idxOf_cons, List.idxOf_cons, ih]
    by_cases h : j = i
    · subst h; simp
    · have h1 : (j == i) = false := by simpa using h
      have h2 : (f j == f i) = false := by simpa using fun h' => h (hf h')
      rw [h1, h2]
end Groundwork
