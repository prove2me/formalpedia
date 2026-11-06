-- Prove2me | solution 1 for GeneralPieces.thmRunningTime_c_m
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:10:16.580063+00:00
-- url     : https://prove2.me/submissions/dfa4ac2d-3ba0-4ad7-ab4f-64e867b1a622

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
import Theorems.Thm_P2M_GeneralPieces_x_Of_ge_2a558e3f9765
import Theorems.Thm_P2M_GeneralPieces_x_Of_pow_e8c07e605600
import Theorems.Thm_GeneralPieces_partC_m_tied
import Theorems.Thm_GeneralPieces_Top_countInRate_of_topM
import Theorems.Thm_GeneralPieces_mayAssume
import Theorems.Thm_GeneralPieces_to_par_one
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_PaddedDescent_F_Price_rho_lt
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen
namespace GeneralPieces
theorem _root_.solution (ρ : ℝ) (c : ℕ) (hE : AppRunningTime.Exist ρ c) : SatM.CountInRate (SatM.rPow (AppRunningTime.alpha' ρ)) := by
  obtain ⟨P, A', val, h⟩ := hE
  obtain ⟨P', h', -, hcap⟩ := mayAssume ρ c P A' val h
  obtain ⟨hP, hKeeps, hm⟩ := to_par_one h' fun tr lam i _ _ => hcap tr lam i
  exact Top.countInRate_of_topM (partC_m_tied h.rho_ge h.rho_lt hP hm hKeeps (x₀Of_ge c) (x₀Of_pow c))
end GeneralPieces
