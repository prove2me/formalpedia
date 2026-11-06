-- Prove2me | solution 1 for GraphProblems.stShortens
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:26:42.793147+00:00
-- url     : https://prove2.me/submissions/cac57e1a-5076-4b23-a355-1212f193a271

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_GraphProblems_DomTree
import Theorems.Thm_GraphProblems_DomTree_cntS_step
import Theorems.Thm_GraphProblems_DomTree_sum_leaves
import Theorems.Thm_GraphProblems_DomTree_inv_bound
import Theorems.Thm_GraphProblems_DomTree_inv_root
import Theorems.Thm_GraphProblems_DomTree_inv_step
import Theorems.Thm_GraphProblems_DomTree_inv_size
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Sparsify_exists_of_mem_leaves
import Theorems.Thm_Groundwork_Sparsify_length_leaves_le
import Theorems.Thm_Groundwork_Sparsify_stack_bound
import Theorems.Thm_Groundwork_Sparsify_step_eq_none_of_mem_leaves
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
import Theorems.Thm_WidthK_Thresholds_exists_tau
import Theorems.Thm_WidthK_Thresholds_sum_choose_le_two_rpow
import Theorems.Thm_WidthK_Thresholds_two_le_bsum
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
open GraphProblems
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Finset DomTree
namespace GraphProblems
theorem _root_.solution : StShortens := by
  intro ε hε
  obtain ⟨w, -, hw4, hw⟩ := WidthK.Thresholds.exists_tau 1 0 hε
  have hw1 : 1 ≤ w := by omega
  refine ⟨w, hw1, fun n s m => ?_⟩
  set L : ℕ := WidthK.bsum w 1 with hL
  have hL2 : 2 ≤ L := WidthK.Thresholds.two_le_bsum w 1
  have hb : ∀ x p t, Inv n s w x p t → p ≤ 2 * n ∧ t ≤ n := inv_bound
  have hs : ∀ x p t l h, Inv n s w x p t → stepD w x = some (l, h) → Inv n s w l (p + 1) t ∧ Inv n s w h (p + 1) (t + w) :=
    inv_step hw1
  have h0 := inv_root n s w m
  refine ⟨?_, fun x hx => ?_, ?_, fun i => ?_⟩
  · have h1 := length_leaves_le hb hs (2 * n) (L * n) (1 * n / w) _ 0 0 h0 (by nlinarith)
      (by have := Nat.lt_mul_div_succ n (show 0 < w by omega); rw [Nat.mul_comm] at this; simpa using this)
    have h2 := WidthK.Thresholds.sum_choose_le_two_rpow hw1 (show 1 ≤ L by omega) (by simpa using hw) n
    exact le_trans (by exact_mod_cast h1) h2
  · have hn := step_eq_none_of_mem_leaves hb hs (2 * n) _ 0 0 h0 (by omega) x hx
    obtain ⟨p', t', hG⟩ := exists_of_mem_leaves hs (2 * n) _ 0 0 h0 x hx
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := inv_size hG
    refine ⟨hn, g1, ?_, by simpa [leafD] using g6⟩
    have hshort : ∀ D ∈ x.2.1, D.length ≤ w := by
      unfold stepD at hn
      have := List.find?_eq_none.1 (Option.map_eq_none_iff.1 hn)
      intro D hD
      simpa using this D hD
    intro B hB
    rcases List.mem_append.1 hB with hB | hB
    · obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hB
      refine ⟨by simpa [posC] using hshort D hD, fun q hq => ?_⟩
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hq
      exact (g3 D hD).2 u hu
    · exact g5 B hB
  · have h1 := sum_leaves (stepD w) (fun x => cntS n s (leafD x).2.2) (fun x l h e => cntS_step e n s) (2 * n)
      (rootD (List.replicate n (), s, m))
    rw [← h1]
    simp [leafD, rootD, domF]
  · obtain ⟨h1, h2⟩ := stack_bound hb hs _ 0 0 h0 i
    refine ⟨h1, fun x hx => ?_⟩
    obtain ⟨p', t', hG⟩ := h2 x hx
    obtain ⟨g1, g2, g3, g4, g5, -⟩ := inv_size hG
    exact ⟨g1, g2, g3, g4, g5⟩
end GraphProblems
