-- Prove2me | solution 1 for GeneralPieces.Top.stCountG2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:41:14.555269+00:00
-- url     : https://prove2.me/submissions/d978aaad-7e2e-4e04-a7a6-84a49d741a9b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_ClauseBound_Alg_TopNet
import Definitions.Def_CountKSat_Value
import Definitions.Def_CountKSat_InOut
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Top_CaseI
import Theorems.Thm_GeneralPieces_Top_sized_mono
import Theorems.Thm_GeneralPieces_Top_pow_le_two_pow
import Theorems.Thm_GeneralPieces_Top_Lof_le_of
import Theorems.Thm_GeneralPieces_Top_one_le_div
import Theorems.Thm_GeneralPieces_Top_val_caseI
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Count_U_wordNet
import Theorems.Thm_Groundwork_Prog_Count_sized_wordNet
import Theorems.Thm_Groundwork_Prog_sized_mono
import Theorems.Thm_Groundwork_SatNet_U_net_le
import Theorems.Thm_Groundwork_TM_Run_trans
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
attribute [local fun_prop] Groundwork.PolyT.length
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
open GeneralPieces GeneralPieces.Top
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Prog.Count PaddedDescent PaddedDescent.F ClauseBound.Alg CountKSat
namespace GeneralPieces.Top
theorem _root_.solution (h : StSatPresentsK) : StCountG := by
  intro Idx _ S ok hS pad i k ψ hi hK _ _ hpad
  have hp : ∀ e, e ≤ needTop S i k ψ.length → 2 ^ e ≤ pad.length := fun e he => (Nat.pow_le_pow_right (by norm_num) he).trans hpad
  have hK0 : 0 < S.K i := by omega
  have hg0 : 0 < 3 * S.K i ^ 8 := by
    have : 0 < S.K i ^ 8 := Nat.pow_pos hK0
    omega
  have hN := h (List.replicate (3 * S.K i ^ 8) ()) (List.replicate k ()) ψ (by rw [List.length_replicate]; exact hg0)
  rw [List.length_replicate, List.length_replicate] at hN
  have hSz : (wordNet (3 * S.K i ^ 8) k ψ).Sized (PtopK (3 * S.K i ^ 8) k ψ.length) 0 := sized_mono (sized_wordNet hg0 0) (le_max_right _ _)
  have hU : (wordNet (3 * S.K i ^ 8) k ψ).U ≤ 2 * k * ψ.length := by
    rw [U_wordNet hg0]
    exact SatNet.U_net_le
  unfold countG
  rw [List.length_replicate]
  refine val_caseI S ok hS satFk _ pad i _ _ 0 _ hi hK hN hSz (Lof_le_of hK0 hU) (by unfold lamTopK; rw [Nat.add_assoc]; exact one_le_div _ hK0) ?_ ?_ ?_ ?_ ?_
  · exact (pow_le_two_pow _ _).trans (hp _ ((le_max_left _ _).trans (le_max_left _ _)))
  · exact hp _ ((Nat.mul_le_mul_left _ (Nat.le_succ _)).trans ((le_max_right _ _).trans (le_max_left _ _)))
  · exact hp _ ((Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans ((le_max_right _ _).trans (le_max_left _ _)))
  · exact hp _ ((le_max_left _ _).trans (le_max_right _ _))
  · have e : bitsS (S.K i) (3 * S.K i ^ 8) (PtopK (3 * S.K i ^ 8) k ψ.length) 0 = PtopK (3 * S.K i ^ 8) k ψ.length * (2 * (3 * S.K i ^ 8) / S.K i) := by
      simp [bitsS]
    rw [e]
    exact hp _ ((le_max_right _ _).trans (le_max_right _ _))
end GeneralPieces.Top
