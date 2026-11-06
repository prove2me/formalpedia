-- Prove2me | solution 1 for GeneralPieces.thmRunningTime_b_tied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:51:30.155227+00:00
-- url     : https://prove2.me/submissions/fc57f2b8-58c7-49c1-aec8-45548ae49e77

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
import Theorems.Thm_GeneralPieces_par_of_isPieces
import Theorems.Thm_GeneralPieces_partB_tied
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_PaddedDescent_F_Price_rho_lt
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen
namespace GeneralPieces
theorem _root_.solution (c : ℕ) : ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (P : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ), AppRunningTime.IsPieces ρ c P A val →
    18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → Tied.PartB (atZero (trimV P val c) c 1) ρ x₀ C₀ := by
  obtain ⟨C₀, hC⟩ := partB_tied c
  refine ⟨C₀, fun ρ x₀ P A val h hx hc => ?_⟩
  obtain ⟨hP, hKeeps, hm⟩ := par_of_isPieces h
  exact hC _ ρ x₀ h.rho_ge h.rho_lt hP hm hKeeps hx hc
end GeneralPieces
