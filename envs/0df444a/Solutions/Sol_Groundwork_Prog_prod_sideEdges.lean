-- Prove2me | solution 1 for Groundwork.Prog.prod_sideEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:27:10.664847+00:00
-- url     : https://prove2.me/submissions/24a44086-12ba-4f43-a883-695eb624cb73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Side
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Prog_GridCount
import Definitions.Def_StepMachines_Prog_SidePresents
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


section
namespace Groundwork.Prog
open Finset Stepped
open Groundwork.Grid (he node c2 sideN sideCap)
private theorem all_range_fin (n : ℕ) (p : ℕ → Bool) : (List.range n).all p = true ↔ ∀ i : Fin n, p i = true := by
  rw [List.all_eq_true]
  exact ⟨fun h i => h i (List.mem_range.2 i.2), fun h i hi => h ⟨i, List.mem_range.1 hi⟩⟩
private theorem prod_ind_range (n : ℕ) (p : ℕ → Bool) :
    ∏ i : Fin n, (if p i = true then (1 : ℤ) else 0) = if (List.range n).all p = true then 1 else 0 := by
  rw [Finset.prod_boole]
  simp only [mem_univ, true_imp_iff, all_range_fin]
end Groundwork.Prog
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped
open Groundwork.Grid (he node c2 sideN sideCap)
namespace Groundwork.Prog
theorem _root_.solution {C : Type} {g : ℕ} {tr : Bool} {lam : C → ℕ} (x : (C × ℕ) × FQ) :
    ∏ i : Fin g,
        (if he g (lam x.1.1) x.2.2.1 i (node g tr x.2.1.2 i) = block (lam x.1.1) i x.2.2.2 then (1 : ℤ) else 0) =
      if sideEdges g tr lam x = true then 1 else 0 := by
  unfold sideEdges
  rw [← prod_ind_range]
  simp only [beq_iff_eq]
end Groundwork.Prog
