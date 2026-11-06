-- Prove2me | solution 1 for GeneralPieces.partB_tied_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:40:17.311075+00:00
-- url     : https://prove2.me/submissions/460445eb-3513-4645-9ad1-8db3e0f3b146

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Tied_Defs
import Definitions.Def_GeneralPieces_Rec_Seq
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Rec_Descend
import Definitions.Def_GeneralPieces_Rec_Level
import Definitions.Def_ClauseBound_Gen_Pick
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_ClauseBound_Alg_Enum
import Definitions.Def_ClauseBound_Alg_Grid
import Definitions.Def_ClauseBound_Alg_CertEnum
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_Alg_CertLevel
import Definitions.Def_PaddedDescent_Col_CertG
import Definitions.Def_GeneralPieces_Rec_PartB
import Theorems.Thm_GeneralPieces_pick_rows
import Theorems.Thm_GeneralPieces_runB_polyT
import Theorems.Thm_ClauseBound_Gen_Rate_step_K
import Theorems.Thm_ClauseBound_Gen_Rate_step_d
import Theorems.Thm_ClauseBound_Gen_Rate_step_p
import Theorems.Thm_GeneralPieces_Chain_levelOK2
import Theorems.Thm_GeneralPieces_Chain_zetaOf_step
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen
namespace GeneralPieces
theorem _root_.solution (hR : StRate2) (hCh : StChain2) (hSolve : ∀ P, StSolveG2 P) (hNeed : ∀ P, StNeedG P) (hCS : ∀ P, StCertSolveG P) (c : ℕ) :
    ∃ C₀ : ℕ, ∀ (P : PiecesF) (ρ : ℝ) (x₀ : ℕ), 1 / 2 ≤ ρ → ρ < 1 → Par P ρ c → P.m = 1 → P.Keeps → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → Tied.PartB P ρ x₀ C₀ := by
  obtain ⟨C₀, hC⟩ := hR c
  refine ⟨C₀, fun P ρ x₀ hρ hρ1 hP hm hKeeps hx hc => ?_⟩
  have hs : ∀ (pad lu : U) (l lam B : ℕ) (I : PInst), WFe (K x₀ l) lam B I →
      Tied.runB P x₀ (pad, lu, I) = solveG P pad (K x₀ 0) (sched P x₀ l) I := fun pad lu l lam B I hI => by
    change solveG P pad (Pick.pick P x₀ (List.replicate I.2.length ())).2.2.length (Pick.pick P x₀ (List.replicate I.2.length ())).2.1 I = _
    rw [pick_rows P x₀ hx l lam B I hI]
    simp [idx, rep]
  refine ⟨runB_polyT P x₀ (hCS P) hKeeps, hs, fun l => ⟨Rate.step_K P x₀ l, Rate.step_p P x₀ l, Rate.step_d P x₀ l, Chain.zetaOf_step hm x₀ l⟩,
    fun l lam hlam => Chain.levelOK2 hP hm x₀ hx l lam hlam, fun pad l lam B I hlam _ hI hpad => ?_, fun l lam B hlam hB => hC P ρ x₀ hρ hρ1 hP hm hx hc l lam B hlam hB⟩
  rw [hs pad _ l lam B I hI]
  exact hSolve P pad (K x₀ 0) (sched P x₀ l) (K x₀ l) lam B I (hCh P ρ c x₀ hP hm hx hc l lam hlam)
    (hNeed P pad.length (K x₀ l) lam B 1 1 (sched P x₀ l) hpad) hI
end GeneralPieces
