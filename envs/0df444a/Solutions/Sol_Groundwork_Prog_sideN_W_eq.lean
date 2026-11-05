-- Prove2me | solution 1 for Groundwork.Prog.sideN_W_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:30:52.120186+00:00
-- url     : https://prove2.me/submissions/53c73c37-8bb0-47d3-907f-8b075bf72835

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Side
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Prog_GridCount
import Definitions.Def_StepMachines_Prog_SidePresents
import Theorems.Thm_Groundwork_Prog_sideChk_iff
import Theorems.Thm_Groundwork_Grid_gridE_symm_val
import Theorems.Thm_Groundwork_Grid_node_lt
import Theorems.Thm_Groundwork_Grid_sideN_W
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
open Groundwork Groundwork.Prog
open Finset Stepped
open Groundwork.Grid (he node c2 sideN sideCap)
namespace Groundwork.Prog
theorem _root_.solution {C : Type} {g : ℕ} {tr : Bool} {lam : C → ℕ} (Rm : Inst (Fin (g * g)) (List Bool)) (c : C) (y : ℕ)
    (a : Fin g) {z : List Bool} (hz : z.length = g ^ 3 * lam c) :
    (sideN g tr (lam c) Rm y).W a z = sideWv g tr (lam c) Rm (sideChk g tr lam ((c, y), (a.val, z))) a z := by
  rw [Grid.sideN_W g tr (lam c) Rm y a hz, sideWv]
  by_cases hc : sideChk g tr lam ((c, y), (a.val, z)) = true
  · obtain ⟨h1, h2⟩ := (sideChk_iff _).1 hc
    rw [if_pos hc, Finset.prod_eq_one (s := pairs (Fin g)) fun q hq => if_pos (h2 q hq), mul_one, Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [if_pos (h1 i), dif_pos (Grid.node_lt tr a.2 i.2)]
    have e : (Grid.gridE g tr).symm (a, i) = ⟨node g tr a i, Grid.node_lt tr a.2 i.2⟩ :=
      Fin.ext (Grid.gridE_symm_val g tr (a, i))
    rw [e]
    congr 1
    funext u
    simp only [sideLabels, Fin.ext_iff]
  · rw [if_neg hc]
    rw [sideChk_iff, not_and_or] at hc
    rcases hc with h | h
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (mem_univ i) (if_neg hi), zero_mul]
    · push Not at h
      obtain ⟨q, hq, hne⟩ := h
      rw [Finset.prod_eq_zero hq (if_neg hne), mul_zero]
end Groundwork.Prog
