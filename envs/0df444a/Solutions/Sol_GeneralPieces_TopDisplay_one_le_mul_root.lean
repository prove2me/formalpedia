-- Prove2me | solution 1 for GeneralPieces.TopDisplay.one_le_mul_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:13:29.942431+00:00
-- url     : https://prove2.me/submissions/0e5434f3-2b3a-4849-94b1-b71b23a9a276

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Theorems.Thm_GeneralPieces_TopDisplay_logb_pow_le_real
import Theorems.Thm_ClauseBound_Alg_TopArith_le_logb_of_pow_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA
namespace GeneralPieces.TopDisplay
theorem _root_.solution (K C₀ d : ℕ) (t e : ℝ) (ht : 1 ≤ t) (hK : 2 ≤ K) (hKt : (K : ℝ) ≤ t ^ d) (he : 1 / Real.logb 2 K ^ C₀ ≤ e) :
    1 ≤ ((d ^ C₀ * (C₀.factorial * 2 ^ C₀) : ℕ) : ℝ) * e * t := by
  have hκ : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have h1 : (1 : ℝ) ≤ Real.logb 2 K := by simpa using le_logb_of_pow_le K 1 (by simpa using hK)
  have hL : 0 < Real.logb 2 K ^ C₀ := by positivity
  have he1 : 1 ≤ e * Real.logb 2 K ^ C₀ := (div_le_iff₀ hL).1 he
  have he0 : 0 ≤ e := le_trans (by positivity) he
  have h2 : Real.logb 2 K ≤ d * Real.logb 2 t := by
    have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hκ hKt
    rwa [Real.logb_pow] at this
  have h3 : Real.logb 2 K ^ C₀ ≤ (d : ℝ) ^ C₀ * ((C₀.factorial * 2 ^ C₀ : ℕ) * t) :=
    calc Real.logb 2 K ^ C₀ ≤ (d * Real.logb 2 t) ^ C₀ := pow_le_pow_left₀ (by linarith) h2 C₀
      _ = (d : ℝ) ^ C₀ * Real.logb 2 t ^ C₀ := mul_pow _ _ _
      _ ≤ (d : ℝ) ^ C₀ * ((C₀.factorial * 2 ^ C₀ : ℕ) * t) := mul_le_mul_of_nonneg_left (logb_pow_le_real t ht C₀) (by positivity)
  calc (1 : ℝ) ≤ e * Real.logb 2 K ^ C₀ := he1
    _ ≤ e * ((d : ℝ) ^ C₀ * ((C₀.factorial * 2 ^ C₀ : ℕ) * t)) := mul_le_mul_of_nonneg_left h3 he0
    _ = ((d ^ C₀ * (C₀.factorial * 2 ^ C₀) : ℕ) : ℝ) * e * t := by push_cast; ring
end GeneralPieces.TopDisplay
