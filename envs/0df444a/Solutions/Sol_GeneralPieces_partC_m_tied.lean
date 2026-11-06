-- Prove2me | solution 1 for GeneralPieces.partC_m_tied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:57:42.130264+00:00
-- url     : https://prove2.me/submissions/9b410343-937f-448a-b615-8bcf3c7a6017

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_GeneralPieces_Rec_PartB
import Definitions.Def_GeneralPieces_Rec_Seq
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_Num_PartD
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Definitions.Def_GeneralPieces_DefGenPieces_MayAssume
import Definitions.Def_ClauseBound_Gen_End
import Definitions.Def_ClauseBound_ParityChecks_MasterOL
import Definitions.Def_GeneralPieces_Top_CaseI
import Definitions.Def_GeneralPieces_Top_EndM
import Definitions.Def_ClauseBound_ParityChecks_MasterOL
import Definitions.Def_ClauseBound_ParityChecks_MasterOL
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Gen
import Definitions.Def_ClauseBound_TopN_Gen
import Definitions.Def_ClauseBound_Alg_NeedC
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_TopVal
import Definitions.Def_ClauseBound_Alg_CertTop
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_ClauseBound_ParityChecks_EndOL
import Definitions.Def_ClauseBound_ParityChecks_TopOL
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Definitions.Def_ClauseBound_ParityChecks_CertOL
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Definitions.Def_ClauseBound_ParityChecks_Ev
import Definitions.Def_ClauseBound_ParityChecks_Count
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Definitions.Def_ClauseBound_ParityChecks_Bridge
import Definitions.Def_ClauseBound_ParityChecks_ChoiceByPotential
import Definitions.Def_ClauseBound_TopN_Budget
import Definitions.Def_ClauseBound_TopN_Walk
import Definitions.Def_ClauseBound_Alg_CertTopNet
import Definitions.Def_PaddedDescent_F_MarkCode
import Definitions.Def_PaddedDescent_F_MarkVal
import Definitions.Def_PaddedDescent_F_MarkProf
import Definitions.Def_PaddedDescent_F_MarkSize
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_CountKSatRate_Tree
import Definitions.Def_CountKSatRate_Walk
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSatRate_Stack
import Definitions.Def_CountKSat_InOut
import Definitions.Def_GeneralPieces_ThmRunningTime
import Theorems.Thm_GeneralPieces_solver_poly
import Theorems.Thm_GeneralPieces_K_idx
import Theorems.Thm_ClauseBound_Alg_CertTop_stCertM
import Theorems.Thm_ClauseBound_Alg_CertTop_stCertSatK
import Theorems.Thm_ClauseBound_Alg_Decode_stCertDecM
import Theorems.Thm_ClauseBound_Alg_Decode_stDecM
import Theorems.Thm_ClauseBound_Alg_Need_stNeedG
import Theorems.Thm_ClauseBound_Alg_TopVal_stCorrectM
import Theorems.Thm_ClauseBound_Alg_TopVal_stSatPresentsK
import Theorems.Thm_ClauseBound_Gen_End_alpha_mem
import Theorems.Thm_ClauseBound_Gen_End_le_rPow
import Theorems.Thm_CountKSatRate_stPaddedW
import Theorems.Thm_CountKSat_ProgC_pick_spec
import Theorems.Thm_GeneralPieces_Chain_stChain2
import Theorems.Thm_GeneralPieces_PartAUse_e_le_rPow
import Theorems.Thm_GeneralPieces_PartD_alpha_mem
import Theorems.Thm_GeneralPieces_TopDisplay_top_arith
import Theorems.Thm_GeneralPieces_Top_stCountG2
import Theorems.Thm_GeneralPieces_Top_topM_of_arith
import Theorems.Thm_GeneralPieces_pick_spec
import Theorems.Thm_GeneralPieces_seq_of_pick
import Theorems.Thm_GeneralPieces_solveG2
import Theorems.Thm_GeneralPieces_stRate2
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_PaddedDescent_F_certRebalG
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen
namespace GeneralPieces
theorem _root_.solution {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hP : Par P ρ c) (hm : P.m = 1) (hKeeps : P.Keeps) (hx : 18 ≤ x₀)
    (hc : c + 5 ≤ 2 ^ x₀) : Tied.PartCm P ρ x₀ := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := pick_spec P x₀
  obtain ⟨C₀, Q, hQ, hpick⟩ := seq_of_pick Chain.stChain2 stRate2 solveG2 Need.stNeedG P ρ c x₀ hρ hρ1 hP hm hx hc (Pick.pick P x₀) hp1 hp2 hp3 hp4
  unfold Tied.PartCm
  rw [← hpick]
  refine Top.topM_of_arith CountKSatRate.stPaddedW (TopVal.stCorrectM Decode.stDecM (Top.stCountG2 TopVal.stSatPresentsK))
    (CertTop.stCertM Decode.stCertDecM CertTop.stCertSatK PaddedDescent.F.certRebalG) (solverOf P) (e ρ x₀) C₀ Q
    ⟨_, fun k m hk hm => TopDisplay.top_arith P ρ x₀ C₀ hρ hx Q hQ k m hk (by rwa [hQ, K_idx] at hm)⟩ (solver_poly P hKeeps) _
    (91 * (3 * x₀ + 6)) (fun m _ => le_rPow (alpha_mem hρ hρ1).2 (by omega) m) fun m _ => ?_
  refine PartAUse.e_le_rPow hρ hρ1 hx ?_
  have h := Q.pick_max (root9 m)
  rwa [hQ, K_idx] at h
end GeneralPieces
