-- Prove2me | solution 1 for GraphProblems.DomTree.inv_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:04:19.73449+00:00
-- url     : https://prove2.me/submissions/fc0aa507-493d-4ab1-b45a-00f07d69f9b0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_GraphProblems_DomTree
import Theorems.Thm_GraphProblems_DomTree_stepD_some
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
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
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length
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
open GraphProblems GraphProblems.DomTree
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Finset
variable {n : ℕ} {a : Fin n → Bool}
namespace GraphProblems.DomTree
theorem _root_.solution {n s w : ℕ} (hw : 1 ≤ w) (x : DNode) (p t : ℕ) (l h : DNode) (hG : Inv n s w x p t) (e : stepD w x = some (l, h)) :
    Inv n s w l (p + 1) t ∧ Inv n s w h (p + 1) (t + w) := by
  obtain ⟨C, hC, hwC, rfl, rfl⟩ := stepD_some e
  obtain ⟨hx, a, V, h1, h2, h3, h4, h5, h6, h7⟩ := hG
  have hlen : (C.take w).length = w := by rw [List.length_take]; omega
  have hHV : ∀ u ∈ C.take w, u ∈ V := fun u hu => (h5 C hC).2 u (List.mem_of_mem_take hu)
  constructor
  · refine ⟨hx, a + 1, V, ?_, by omega, h3, h4, fun D hD => h5 D (List.mem_of_mem_filter hD), by simp only [List.length_cons]; omega, ?_⟩
    · have : (x.2.1.filter fun D => D != C).length < x.2.1.length :=
        List.length_filter_lt_length_iff_exists.2 ⟨C, hC, by simp⟩
      simp only
      omega
    · intro B hB
      rcases List.mem_cons.1 hB with rfl | hB
      · refine ⟨by simp [posC], fun q hq => ?_⟩
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hq
        exact h4 u (hHV u hu)
      · exact h7 B hB
  · refine ⟨hx, a, V \ (C.take w).toFinset, by simpa using h1, by omega, ?_, fun u hu => h4 u (mem_sdiff.1 hu).1, ?_, ?_, ?_⟩
    · have hsub : (C.take w).toFinset ⊆ V := fun u hu => hHV u (List.mem_toFinset.1 hu)
      have hc := card_sdiff_add_card_eq_card hsub
      have hn : #(C.take w).toFinset = w := by
        rw [List.toFinset_card_of_nodup ((h5 C hC).1.sublist (List.take_sublist w C)), hlen]
      omega
    · intro D' hD'
      obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hD'
      refine ⟨(h5 D hD).1.filter _, fun u hu => ?_⟩
      obtain ⟨hu1, hu2⟩ := List.mem_filter.1 hu
      exact mem_sdiff.2 ⟨(h5 D hD).2 u hu1, by simpa using hu2⟩
    · simp only [List.length_append, List.length_map, hlen]
      omega
    · intro B hB
      rcases List.mem_append.1 hB with hB | hB
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hB
        exact ⟨by simpa using hw, fun q hq => by
          obtain rfl : q = (u, false) := by simpa using hq
          exact h4 u (hHV u hu)⟩
      · exact h7 B hB
end GraphProblems.DomTree
