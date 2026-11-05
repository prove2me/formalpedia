-- Prove2me | solution 1 for GraphProblems.stDecide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:29:22.577127+00:00
-- url     : https://prove2.me/submissions/a5ae0962-733e-4b3b-ac30-2fcffc24a93a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
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
open Sets
namespace GraphProblems
theorem _root_.solution : StDecide := fun n G s hs => by
  have hne : ∀ P : Finset (Fin n) → Prop, {S : Finset (Fin n) | P S}.ncard ≠ 0 ↔ ∃ S, P S := fun P => by
    rw [← pos_iff_ne_zero, Set.ncard_pos]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [numIndepSets, hne]
    constructor
    · rintro ⟨S, hS, hc⟩
      obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq hc
      exact ⟨T, ⟨Set.Pairwise.mono (coe_subset.2 hT) hS, hTc⟩⟩
    · rintro ⟨S, hS⟩
      exact ⟨S, hS.1, hS.2.ge⟩
  · rw [numCliques, hne]
    constructor
    · rintro ⟨S, hS, hc⟩
      obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq hc
      exact ⟨T, ⟨hS.subset (coe_subset.2 hT), hTc⟩⟩
    · rintro ⟨S, hS⟩
      exact ⟨S, hS.1, hS.2.ge⟩
  · rw [numVertexCovers, hne]
    constructor
    · rintro ⟨S, hS, hc⟩
      obtain ⟨T, hT, -, hTc⟩ := exists_subsuperset_card_eq (subset_univ S) hc (by simpa using hs)
      exact ⟨T, hS.subset (coe_subset.2 hT), hTc⟩
    · rintro ⟨S, hS, hc⟩
      exact ⟨S, hS, hc.le⟩
  · rw [numDominatingSets, hne]
    constructor
    · rintro ⟨S, hS, hc⟩
      obtain ⟨T, hT, -, hTc⟩ := exists_subsuperset_card_eq (subset_univ S) hc (by simpa using hs)
      refine ⟨T, fun v => ?_, hTc⟩
      rcases hS v with h | ⟨u, hu, huv⟩
      · exact Or.inl (hT h)
      · exact Or.inr ⟨u, hT hu, huv⟩
    · rintro ⟨S, hS, hc⟩
      exact ⟨S, hS, hc.le⟩
end GraphProblems
