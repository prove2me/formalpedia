-- Prove2me | solution 1 for MainRoute.meetsBoundInM_of_topM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:41:41.261593+00:00
-- url     : https://prove2.me/submissions/64bff96b-0c56-46a0-8668-f49e8e8455a3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainRoute_GeneralDefs
import Definitions.Def_MainRoute_EveryMachine
import Definitions.Def_GeneralPieces_Top_EndM
import Definitions.Def_GeneralPieces_Top_CaseI
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_ClauseBound_Gen_End
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Alg_TopVal
import Definitions.Def_ClauseBound_Alg_CertTop
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_PaddedDescent_Col_CertG
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MainRoute_GeneralInM
import Theorems.Thm_GeneralPieces_Series_cf_add
import Theorems.Thm_GeneralPieces_Series_cf_neg
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_cf_sub
import Theorems.Thm_GeneralPieces_Series_cf_zero
import Theorems.Thm_GeneralPieces_Trim_length_bitsOf
import Theorems.Thm_GeneralPieces_Trim_length_rep
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
import Theorems.Thm_MainRoute_steps_le_of_exponent_le
import Theorems.Thm_PaddedDescent_F_Top_correct
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
theorem _root_.solution {Idx : Type} [Enc Idx] {S : Solver Idx} {pick : U → U × Idx} (hT : GeneralPieces.Tied.TopM S pick (SatM.rPow (1 / 2)))
    (M : TM2ComputableAux Bool Bool) (q : ℕ) (hM : Computes M (AM S pick) (eM S pick) q) : ∃ C : ℕ, MeetsBoundInM M C := by
  obtain ⟨G, hG⟩ := hT.rate
  refine ⟨2 * q + 2 * q * (G + 1) + q * 4 ^ q, fun k n φ hk hφ hm hocc => ?_⟩
  have hm1 : 1 ≤ φ.length := by omega
  have hx : Outputs M (SatM.enc k φ) (AM S pick (SatM.enc k φ, pad (eM S pick (SatM.enc k φ)))) (q * ((SatM.enc k φ).length + 2 ^ eM S pick (SatM.enc k φ) + 1) ^ q) := hM (SatM.enc k φ)
  rw [hT.correct k n φ hk hm1 hφ hocc (pad _) (by simp [pad])] at hx
  obtain ⟨ev⟩ := hx
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩
  have hX : 1 ≤ expM k φ.length := le_trans (by norm_num) (VariableBound.Paper.two_le_expM hk hm)
  have hE : (eM S pick (SatM.enc k φ) : ℝ) ≤ G * expM k φ.length :=
    (hG k n φ hk hm1 hφ hocc).trans (mul_le_mul_of_nonneg_left (VariableBound.Paper.shiftM_le k hm) (by positivity))
  have hL : 1 ≤ (SatM.enc k φ).length := by
    simp only [SatM.enc, List.length_append, List.length_cons]
    omega
  exact steps_le_of_exponent_le q G hX hE hL
end MainRoute
