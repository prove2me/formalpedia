-- Prove2me | solution 1 for Groundwork.Grid.ZW_eq_Z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:08:11.837308+00:00
-- url     : https://prove2.me/submissions/acaef087-0356-4d85-a878-85a92d8db546

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_CutWord
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_StepMachines_Prog_Brute
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_StepMachines_Math_SideCodes
import Theorems.Thm_Groundwork_Code_bijOn_enc
import Theorems.Thm_Groundwork_Grid_bitsC_full
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
import Theorems.Thm_Groundwork_sum_tuples_map
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
namespace Groundwork.Grid
theorem _root_.solution {K : ℕ} (n : ℕ) (Rm : Inst (Fin K) (List Bool)) (d : Bits n) : Inst.ZW n [] Rm = (instW n Rm).Z d := by
  unfold Inst.ZW Inst.Z labellings
  have hb : Set.BijOn (bitsC n).enc (univ : Finset (Bits n)) (words n) := by
    have := (bitsC n).bijOn_enc
    rwa [bitsC_full] at this
  rw [sum_tuples_map (fun p : Fin K × Fin K => p.1 < p.2) (T := fun _ => words n)
    (T' := fun _ => (univ : Finset (Bits n))) [] d (fun _ => (bitsC n).enc) (fun _ _ => hb)]
  refine sum_congr rfl fun Λ _ => prod_congr rfl fun v _ => ?_
  unfold instW
  congr 1
  funext u
  unfold star pr
  by_cases h : u = v
  · subst h; simp
  · have : min v u < max v u := min_lt_max.2 (Ne.symm h)
    simp [h, this]
end Groundwork.Grid
