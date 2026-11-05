-- Prove2me | solution 1 for Groundwork.Grid.abs_sideR_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:13:01.977509+00:00
-- url     : https://prove2.me/submissions/fd36dc80-151c-4711-8465-8a6d41a5eca2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_CutWord
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_StepMachines_Prog_Brute
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_StepMachines_Math_SideCodes
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
namespace Groundwork.Grid
theorem _root_.solution {g n B : ℕ} (tr : Bool) {Rm : Inst (Fin (g * g)) (List Bool)} (hR : Prog.BoundedInst n B Rm)
    (w : Fin g × Fin g) (h : Fin g × Fin g → Bits n) : |sideR g tr n Rm w h| ≤ 2 ^ B := by
  unfold sideR onGrid
  split_ifs
  · refine hR _ _ (fun u hu => ?_) (by simp)
    rw [if_neg hu]
    exact (bitsC n).length_enc (mem_univ _)
  · rw [abs_zero]
    positivity
end Groundwork.Grid
