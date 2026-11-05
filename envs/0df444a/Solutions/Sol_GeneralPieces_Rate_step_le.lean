-- Prove2me | solution 1 for GeneralPieces.Rate.step_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:27:13.455912+00:00
-- url     : https://prove2.me/submissions/b499405b-110f-4dfb-bf42-0f08b09ac59d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_GeneralPieces_Rate_first_le
import Theorems.Thm_GeneralPieces_Rate_size_nPat_le
import Theorems.Thm_GeneralPieces_Rate_size_cnt_le
import Theorems.Thm_P2M_GeneralPieces_Rate_K2L_le__0b58532c6456
import Theorems.Thm_GeneralPieces_Rate_log_child
import Theorems.Thm_GeneralPieces_Rate_c_lam_le
import Theorems.Thm_GeneralPieces_Rate_three_le
import Theorems.Thm_GeneralPieces_Rate_st_le
import Theorems.Thm_GeneralPieces_Rate_half_const
import Theorems.Thm_GeneralPieces_Rate_step_real
import Theorems.Thm_ClauseBound_Gen_Rate_Bd_succ
import Theorems.Thm_ClauseBound_Gen_Rate_K_le_g
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K
import Theorems.Thm_ClauseBound_Gen_Rate_col_le
import Theorems.Thm_ClauseBound_Gen_Rate_needG_succ
import Theorems.Thm_ClauseBound_Gen_Rate_one_le_lamNext
import Theorems.Thm_ClauseBound_Gen_Rate_one_le_log
import Theorems.Thm_ClauseBound_Gen_Rate_pot_real
import Theorems.Thm_ClauseBound_Gen_Rate_size_nPat_le
import Theorems.Thm_ClauseBound_Gen_Rate_zeta_le
import Theorems.Thm_GeneralPieces_PartAUse_e_le_one
import Theorems.Thm_GeneralPieces_PartAUse_e_nonneg
import Theorems.Thm_GeneralPieces_PartA_thmRunningTime_a
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
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
attribute [local fun_prop] Groundwork.PolyT.all
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
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (hc : c + 5 ≤ 2 ^ x₀) (l : ℕ)
    (IH : ∀ lam B cnt z : ℕ, 1 ≤ lam →
      (needG P (K x₀ l) lam B cnt z (sched P x₀ l) : ℝ) ≤ Nat.size cnt + Nat.size (z + Nat.size cnt) + Bd ρ c x₀ l lam B)
    (lam B cnt z : ℕ) (hlam : 1 ≤ lam) :
    (needG P (K x₀ (l + 1)) lam B cnt z (sched P x₀ (l + 1)) : ℝ) ≤ Nat.size cnt + Nat.size (z + Nat.size cnt) + Bd ρ c x₀ (l + 1) lam B := by
  have hfirst := first_le (ρ := ρ) (c := c) hρ hρ1 hx (l + 1) lam B cnt z hlam
  have hA := PartA.thmRunningTime_a ρ x₀ hρ hρ1 hx
  have hρ0 : 0 ≤ ρ := by linarith
  rw [needG_succ, Nat.cast_max]
  refine max_le hfirst ?_
  have n3 := big_le_K hx l
  have hk1 : (1 : ℝ) ≤ K x₀ l := by exact_mod_cast (by omega : 1 ≤ K x₀ l)
  have hka : (K x₀ l : ℝ) ≤ g x₀ l := by exact_mod_cast K_le_g x₀ l
  have hre : (ρ + 3 * zeta l) * e ρ x₀ l ≤ e ρ x₀ (l + 1) := by
    rw [show e ρ x₀ (l + 1) = (ρ + 3 * zeta l) * e ρ x₀ l + 3 / (K x₀ l : ℝ) from rfl]
    have : 0 ≤ 3 / (K x₀ l : ℝ) := by positivity
    linarith
  have hhalf : 2 * ((c + 5) * K x₀ l ^ 2) ≤ g x₀ l ^ 4 := by have := half_const hx hc l; omega
  have hneed : K x₀ l * P.need 0 lam ≤ g x₀ l ^ 4 * lam :=
    (Nat.mul_le_mul_left _ (hP.need 0 lam hlam)).trans (c_lam_le hx hc l lam)
  rw [Bd_succ]
  simp only [Nat.cast_max, Nat.cast_zero]
  exact step_real _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (IH _ _ _ _ (one_le_lamNext _ _ _)) (size_cnt_le hP hx l lam B cnt hlam) (size_nPat_le hP hx l lam B hlam)
    (pot_real hP hx l lam B cnt z hlam) (K2L_le' hP hm hx l lam B hlam) (log_child hP hm hx l lam B hlam)
    (by exact_mod_cast hhalf) hk1 (hka.trans (le_self_pow₀ (hk1.trans hka) (by norm_num)))
    (by positivity) (by exact_mod_cast hlam) (one_le_log hx (l + 1) lam B hlam) (three_le hA hρ0 l)
    (PartAUse.e_nonneg hA hρ0 l) (PartAUse.e_le_one hA hρ0 hρ1.le l) (PartAUse.e_nonneg hA hρ0 (l + 1)) hre (by have := zeta_le l; linarith)
    (by exact_mod_cast hneed) (col_le hx l) (st_le hm l lam)
    (by exact_mod_cast Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (by positivity) (by positivity)
end GeneralPieces.Rate
