-- Prove2me | solution 1 for MainRoute.boundInMForEveryMachine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:27:39.639329+00:00
-- url     : https://prove2.me/submissions/fc99553d-0963-4dc3-aede-697ad24e3d8d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainRoute_Defs
import Definitions.Def_RecursionWithPieces_Main
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_VariableBound_Paper_Rename_Time
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_MainRoute_EveryMachine
import Theorems.Thm_MainRoute_steps_le_of_exponent_le
import Theorems.Thm_GeneralPieces_Asymptotic_alpha_half
import Theorems.Thm_GeneralPieces_Series_cf_add
import Theorems.Thm_GeneralPieces_Series_cf_neg
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_cf_sub
import Theorems.Thm_GeneralPieces_Series_cf_zero
import Theorems.Thm_GeneralPieces_Trim_length_bitsOf
import Theorems.Thm_GeneralPieces_Trim_length_rep
import Theorems.Thm_GeneralPieces_thmRunningTime_c_m_tied
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
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
import Theorems.Thm_PaddedDescent_F_Top_correct
import Theorems.Thm_VariableBound_Net_Main_val
import Theorems.Thm_VariableBound_Paper_shiftM_le
import Theorems.Thm_VariableBound_Paper_two_le_expM
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] GeneralPieces.Series.cf_add
attribute [local simp] GeneralPieces.Series.cf_neg
attribute [local simp] GeneralPieces.Series.cf_smul
attribute [local simp] GeneralPieces.Series.cf_sub
attribute [local simp] GeneralPieces.Series.cf_zero
attribute [local simp] GeneralPieces.Trim.length_bitsOf
attribute [local simp] GeneralPieces.Trim.length_rep
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
open MainRoute
open Turing Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound
open Sat3 (CNF)
namespace MainRoute
theorem _root_.solution : BoundInMForEveryMachine := by
  intro c P₀ A val h
  have hT : GeneralPieces.Tied.TopM (RecursionWithPieces.solverAB P₀ val c) (RecursionWithPieces.pickAB P₀ val c) (SatM.rPow (AppRunningTime.alpha' (1 / Real.sqrt 2))) := GeneralPieces.thmRunningTime_c_m_tied h
  have hα : AppRunningTime.alpha' (1 / Real.sqrt 2) = 1 / 2 := GeneralPieces.Asymptotic.alpha_half
  rw [hα] at hT
  refine ⟨?_, fun M q hM => ?_⟩
  · obtain ⟨N, q, -, hfin, hN, -⟩ := hT.machine
    exact ⟨N, q, hfin, hN⟩
  · obtain ⟨G, hG⟩ := hT.rate
    refine ⟨2 * q + 2 * q * (G + 1) + q * 4 ^ q, fun k n φ hk hφ hm hocc => ?_⟩
    have hm1 : 1 ≤ φ.length := by omega
    have hx : Outputs M (SatM.enc k φ) (AM (RecursionWithPieces.solverAB P₀ val c) (RecursionWithPieces.pickAB P₀ val c) (SatM.enc k φ, pad (eM (RecursionWithPieces.solverAB P₀ val c) (RecursionWithPieces.pickAB P₀ val c) (SatM.enc k φ))))
        (q * ((SatM.enc k φ).length + 2 ^ eM (RecursionWithPieces.solverAB P₀ val c) (RecursionWithPieces.pickAB P₀ val c) (SatM.enc k φ) + 1) ^ q) := hM (SatM.enc k φ)
    rw [hT.correct k n φ hk hm1 hφ hocc (pad _) (by simp [pad])] at hx
    obtain ⟨ev⟩ := hx
    refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩
    have hX : 1 ≤ expM k φ.length := le_trans (by norm_num) (VariableBound.Paper.two_le_expM hk hm)
    have hE : (eM (RecursionWithPieces.solverAB P₀ val c) (RecursionWithPieces.pickAB P₀ val c) (SatM.enc k φ) : ℝ) ≤ G * expM k φ.length :=
      (hG k n φ hk hm1 hφ hocc).trans (mul_le_mul_of_nonneg_left (VariableBound.Paper.shiftM_le k hm) (by positivity))
    have hL : 1 ≤ (SatM.enc k φ).length := by
      simp only [SatM.enc, List.length_append, List.length_cons]
      omega
    exact steps_le_of_exponent_le q G hX hE hL
end MainRoute
