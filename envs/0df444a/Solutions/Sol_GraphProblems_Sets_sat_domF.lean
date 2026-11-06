-- Prove2me | solution 1 for GraphProblems.Sets.sat_domF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:59:58.422341+00:00
-- url     : https://prove2.me/submissions/af655cbb-1193-455e-98ef-a1458198804f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Theorems.Thm_GraphProblems_Sets_mem_trueSet
import Theorems.Thm_GraphProblems_stAdj
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
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
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
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
open GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
open GraphProblems.Sets
variable {n : ℕ}
variable (G : SimpleGraph (Fin n)) (a : Fin n → Bool)
namespace GraphProblems.Sets
theorem _root_.solution : (∀ C ∈ domF n (matrix G), ∃ l ∈ C, CountKSat.ext a l.1 = l.2) ↔ IsDominating G (trueSet a) := by
  constructor
  · intro H v
    obtain ⟨l, hl, hal⟩ := H (posC (v.val :: (List.range n).filter fun u => u != v.val && adjB n (matrix G) v.val u))
      (List.mem_map.2 ⟨_, List.mem_map.2 ⟨v.val, List.mem_range.2 v.2, rfl⟩, rfl⟩)
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hl
    rcases List.mem_cons.1 hu with rfl | hu
    · left
      simpa [CountKSat.ext, v.2, mem_trueSet] using hal
    · right
      obtain ⟨hun, huv⟩ := List.mem_filter.1 hu
      rw [List.mem_range] at hun
      simp only [Bool.and_eq_true, bne_iff_ne] at huv
      refine ⟨⟨u, hun⟩, ?_, (stAdj n G v ⟨u, hun⟩).1 huv.2⟩
      simpa [CountKSat.ext, hun, mem_trueSet] using hal
  · intro H C hC
    obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hC
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hD
    rw [List.mem_range] at hv
    rcases H ⟨v, hv⟩ with h | ⟨u, hu, huv⟩
    · refine ⟨(v, true), List.mem_map.2 ⟨v, by simp, rfl⟩, ?_⟩
      simpa [CountKSat.ext, hv, mem_trueSet] using h
    · refine ⟨(u.val, true), List.mem_map.2 ⟨u.val, List.mem_cons_of_mem _ (List.mem_filter.2 ⟨List.mem_range.2 u.2, ?_⟩), rfl⟩, ?_⟩
      · simp only [Bool.and_eq_true, bne_iff_ne]
        exact ⟨fun e => huv.ne (Fin.ext e.symm), (stAdj n G ⟨v, hv⟩ u).2 huv⟩
      · simpa [CountKSat.ext, u.2, mem_trueSet] using hu
end GraphProblems.Sets
