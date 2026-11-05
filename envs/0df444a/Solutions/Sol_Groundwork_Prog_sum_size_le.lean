-- Prove2me | solution 1 for Groundwork.Prog.sum_size_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:57:29.063681+00:00
-- url     : https://prove2.me/submissions/081baca6-3816-4413-90b4-4b1a8eea9aba

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_ThreeSatStatement
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_StepMachines_Prog_Sat
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
open Groundwork.Sparsify (leaves rootP stepP)
namespace Groundwork.Prog
theorem _root_.solution {α : Type} [HasSize α] {s : ℕ} (l : List α) (hs : ∀ x ∈ l, size x ≤ s) :
    (l.map fun x => size x + 1).sum ≤ l.length * (s + 1) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have h1 := hs x (by simp)
    have h2 := ih fun y hy => hs y (by simp [hy])
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega
end Groundwork.Prog
