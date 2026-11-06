-- Prove2me | solution 1 for MainRoute.topM_of_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:10:51.389999+00:00
-- url     : https://prove2.me/submissions/eedfd86f-6ddd-4b5b-85be-de240f9c9a35

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
import Theorems.Thm_MainRoute_e_le_rPow_of_sqrt
import Theorems.Thm_ClauseBound_Alg_CertTop_stCertM
import Theorems.Thm_ClauseBound_Alg_CertTop_stCertSatK
import Theorems.Thm_ClauseBound_Alg_Decode_stCertDecM
import Theorems.Thm_ClauseBound_Alg_Decode_stDecM
import Theorems.Thm_ClauseBound_Alg_TopVal_stCorrectM
import Theorems.Thm_ClauseBound_Alg_TopVal_stSatPresentsK
import Theorems.Thm_ClauseBound_Gen_End_le_rPow
import Theorems.Thm_CountKSatRate_stPaddedW
import Theorems.Thm_GeneralPieces_TopDisplay_stTopArith2
import Theorems.Thm_GeneralPieces_Top_stCountG2
import Theorems.Thm_GeneralPieces_Top_topM_of_arith
import Theorems.Thm_PaddedDescent_F_certRebalG


set_option autoImplicit false
section
section
open MainRoute
open Turing Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound
open Sat3 (CNF)
namespace MainRoute
theorem _root_.solution {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀) (hS : S.Poly) {a : ℕ} (ha : ∀ l : ℕ, e l ≤ a / Real.sqrt (lg (S.K (Q.idx l)))) :
    GeneralPieces.Tied.TopM S Q.pick (SatM.rPow (1 / 2)) :=
  GeneralPieces.Top.topM_of_arith CountKSatRate.stPaddedW (TopVal.stCorrectM Decode.stDecM (GeneralPieces.Top.stCountG2 TopVal.stSatPresentsK))
    (CertTop.stCertM Decode.stCertDecM CertTop.stCertSatK PaddedDescent.F.certRebalG) S e C₀ Q (GeneralPieces.TopDisplay.stTopArith2 Idx S e C₀ Q) hS _
    (a * (9 * C₀ + 1) + 1) (fun m _ => ClauseBound.Gen.End.le_rPow (by norm_num) (by omega) m) fun m _ => e_le_rPow_of_sqrt Q ha m
end MainRoute
