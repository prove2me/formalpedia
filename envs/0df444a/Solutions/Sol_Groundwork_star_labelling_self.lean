-- Prove2me | solution 1 for Groundwork.star_labelling_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:45:36.059533+00:00
-- url     : https://prove2.me/submissions/61391314-dbdb-493b-87f2-a3f89a7832e3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Definitions.Def_StepMachines_Prog_Brute
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
    star (labelling K ℓ d w) v v = d := by
  have : ¬ (pr v v).1 < (pr v v).2 := by simp [pr]
  unfold star labelling
  rw [if_neg this]
end Groundwork
