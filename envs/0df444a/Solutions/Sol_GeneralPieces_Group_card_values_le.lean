-- Prove2me | solution 1 for GeneralPieces.Group.card_values_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:43:49.512073+00:00
-- url     : https://prove2.me/submissions/2fb9f8da-aae4-4b0f-b0f3-d692f2fee8df

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Group_CaseI
import Definitions.Def_GeneralPieces_Group_CaseII
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_Col_CertG
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_GeneralPieces_Group_Lemma
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_congr
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
import Theorems.Thm_Groundwork_TM_update_withIO
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
attribute [local simp] Groundwork.Host.upd_none
attribute [local simp] Groundwork.Host.withIO_none
attribute [local simp] Groundwork.Host.withIO_some
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
attribute [local simp] Groundwork.TM.update_withIO
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
open GeneralPieces GeneralPieces.Group
open Finset Groundwork
variable {J J' σ τ A : Type*}
namespace GeneralPieces.Group
theorem _root_.solution [Fintype J] [LinearOrder J] [Fintype J'] [DecidableEq J'] (χ : J → J') (G : J') :
    #{a | χ a = G} + #{p ∈ pairs J | χ p.1 = G ∧ χ p.2 = G} + ∑ G' ∈ univ.erase G, #{p : J × J | χ p.1 = G ∧ χ p.2 = G'} ≤ Fintype.card J ^ 2 := by
  have hA : #{a | χ a = G} ≤ #{p : J × J | p.1 = p.2 ∧ χ p.1 = G} :=
    Finset.card_le_card_of_injOn (fun a => (a, a)) (by intro a ha; simpa using ha) (by intro a _ b _ e; exact (Prod.mk.inj e).1)
  have hB : #{p ∈ pairs J | χ p.1 = G ∧ χ p.2 = G} = #{p : J × J | p.1 < p.2 ∧ χ p.1 = G ∧ χ p.2 = G} := by
    rw [pairs, Finset.filter_filter]
  have hC : ∑ G' ∈ univ.erase G, #{p : J × J | χ p.1 = G ∧ χ p.2 = G'} = #{p : J × J | χ p.1 = G ∧ χ p.2 ≠ G} := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : J × J => χ p.2) (t := univ.erase G) (by intro p hp; simp at hp ⊢; exact hp.2)]
    refine Finset.sum_congr rfl fun G' hG' => ?_
    have hne : G' ≠ G := by simpa using hG'
    rw [Finset.filter_filter]
    congr 1
    ext p
    simp only [mem_filter, mem_univ, true_and]
    grind
  rw [hB, hC]
  calc _ ≤ #{p : J × J | p.1 = p.2 ∧ χ p.1 = G} + #{p : J × J | p.1 < p.2 ∧ χ p.1 = G ∧ χ p.2 = G} + #{p : J × J | χ p.1 = G ∧ χ p.2 ≠ G} := by omega
    _ = ∑ p : J × J, ((if p.1 = p.2 ∧ χ p.1 = G then 1 else 0) + (if p.1 < p.2 ∧ χ p.1 = G ∧ χ p.2 = G then 1 else 0) +
          (if χ p.1 = G ∧ χ p.2 ≠ G then 1 else 0)) := by simp only [Finset.card_filter, Finset.sum_add_distrib]
    _ ≤ ∑ _p : J × J, 1 := Finset.sum_le_sum fun p _ => by split_ifs <;> first | omega | (exfalso; grind)
    _ = Fintype.card J ^ 2 := by simp [sq]
end GeneralPieces.Group
