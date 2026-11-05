-- Prove2me | solution 1 for Groundwork.Prog.Count.bijOn_bits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:20:23.872748+00:00
-- url     : https://prove2.me/submissions/8f90ba1d-b3c1-45f2-8527-85f949469678

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Theorems.Thm_Groundwork_Prog_Count_loc_lt
import Theorems.Thm_Groundwork_Prog_Count_exists_loc
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
import Theorems.Thm_P2M_Groundwork_SatNet_mul_add_inj__c1cceb82cc73
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
theorem _root_.solution : Set.BijOn (bits (μ := μ) (k := k)) (words (μ * k)) (univ : Finset (Sl μ k → Bool)) := by
  refine ⟨fun _ _ => by simp, fun z hz z' hz' h => ?_, fun f _ => ?_⟩
  · have hl : z.length = μ * k := mem_words.1 hz
    have hl' : z'.length = μ * k := mem_words.1 hz'
    refine List.ext_getElem (hl.trans hl'.symm) fun r h1 h2 => ?_
    obtain ⟨s, rfl⟩ := exists_loc (μ := μ) (k := k) (hl ▸ h1)
    have := congrFun h s
    simpa [bits, List.getD_eq_getElem?_getD, h1, h2] using this
  · classical
    refine ⟨(List.range (μ * k)).map fun r => if h : r < μ * k then f (exists_loc h).choose else false,
      mem_words.2 (by simp), funext fun s => ?_⟩
    have hs := loc_lt s
    have hinj : (exists_loc hs).choose = s := by
      have h := (exists_loc hs).choose_spec
      generalize (exists_loc hs).choose = s' at h
      obtain ⟨h1, h2⟩ := SatNet.mul_add_inj' s'.2.2 s.2.2 h
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    simp [bits, List.getD_eq_getElem?_getD, hs, hinj]
end Groundwork.Prog.Count
