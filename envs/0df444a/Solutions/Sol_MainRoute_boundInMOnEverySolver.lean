-- Prove2me | solution 1 for MainRoute.boundInMOnEverySolver
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:04:25.018839+00:00
-- url     : https://prove2.me/submissions/c4699f0f-4b74-42ee-93b8-25cebe57c2d7

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
import Theorems.Thm_MainRoute_topM_of_sqrt
import Theorems.Thm_MainRoute_meetsBoundInM_of_topM

set_option autoImplicit false
section
section
open MainRoute
open Turing Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound
open Sat3 (CNF)
namespace MainRoute
theorem _root_.solution : BoundInMOnEverySolver := by
  intro Idx _ S e C₀ Q hS a ha
  have hT := topM_of_sqrt Q hS ha
  refine ⟨?_, meetsBoundInM_of_topM hT⟩
  obtain ⟨N, q, -, hfin, hN, -⟩ := hT.machine
  exact ⟨N, q, hfin, hN⟩
end MainRoute
