-- Prove2me | solution 1 for NamesInOrder.everyDirectAlternation_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:57:51.618904+00:00
-- url     : https://prove2.me/submissions/93c8322a-3573-4063-b52e-4f73ade32724

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NamesInOrder_Defs
import Definitions.Def_MainRoute_GeneralMain
import Definitions.Def_MainRoute_General
import Definitions.Def_MainRoute_EveryMachine
import Definitions.Def_TwoMachines_Main
import Definitions.Def_MinOfBounds_Main
import Definitions.Def_MinOfBounds_Rename
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_PairsToBound_Main
import Definitions.Def_Wrap_Main
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Forms
import Definitions.Def_GeneralPieces_Main
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Tied_Bound
import Definitions.Def_NamesInOrder_Chain
import Theorems.Thm_GeneralPieces_Ring_Bd_mono
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
import Theorems.Thm_VariableBound_Paper_corMinIsMainTheorem
import Theorems.Thm_Wrap_Outputs_mono


set_option autoImplicit false
section
section
open NamesInOrder
open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound MainRoute
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution (hCost : AlternationCostGoesIntoC) : EveryDirectAlternationMeetsTheBound := by
  intro M₁ C₁ h₁ M₂ C₂ h₂ N q hN
  obtain ⟨C, hC⟩ := hCost C₁ C₂ q
  have h : MainTheoremFor N C := fun k n φ hk hφ hm hn hocc =>
    Outputs.mono (hN (SatM.enc k φ) _ _ _ _ (h₁ k n φ hk hφ hm hocc) (h₂ k n φ hk hn hφ) rfl) (hC k n φ hk hφ hm hn hocc)
  exact ⟨C, (VariableBound.Paper.corMinIsMainTheorem N C).2 h, h⟩
end NamesInOrder
