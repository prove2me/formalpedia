-- Prove2me | solution 1 for Groundwork.query0_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:55:03.918478+00:00
-- url     : https://prove2.me/submissions/e2b701da-4d0c-4e54-9d52-35e23c9887ca

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Definitions.Def_StepMachines_Prog_Brute
import Theorems.Thm_Groundwork_star_labelling_self
import Theorems.Thm_Groundwork_star_labelling_ne
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
open Finset Stepped
namespace Groundwork
theorem _root_.solution (K ℓ : ℕ) (d w : List Bool) (v : Fin K) :
    query0 K ℓ d w v = (v.1, List.ofFn (star (labelling K ℓ d w) v)) := by
  unfold query0
  congr 1
  refine List.ext_getElem (by simp) fun u h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  have hu : u < K := by simpa using h1
  by_cases huv : u = v.1
  · have : (⟨u, hu⟩ : Fin K) = v := Fin.ext huv
    rw [if_pos huv, this, star_labelling_self]
  · have hne : (⟨u, hu⟩ : Fin K) ≠ v := fun h => huv (by rw [← h])
    rw [if_neg huv, star_labelling_ne K ℓ d w hne]
end Groundwork
