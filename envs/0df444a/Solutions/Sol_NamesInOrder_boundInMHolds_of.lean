-- Prove2me | solution 1 for NamesInOrder.boundInMHolds_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:37:20.52001+00:00
-- url     : https://prove2.me/submissions/abc2292a-0f42-4fa9-95c7-33114b800e68

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
import Theorems.Thm_AppRunningTime_thmHalfPieces
import Theorems.Thm_GeneralPieces_thmHalfPieces
import Theorems.Thm_GeneralPieces_thmHalfPieces_iff
import Theorems.Thm_MainRoute_boundInMForEveryMachine
import Theorems.Thm_VariableBound_Net_Main_val


set_option autoImplicit false
section
section
open NamesInOrder
open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound MainRoute
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution (hAll : ForAllPieces) : BoundInMHolds := by
  obtain ⟨c, P₀, A', val, h⟩ := GeneralPieces.thmHalfPieces_iff.1 AppRunningTime.thmHalfPieces
  obtain ⟨n₀, hn₀⟩ := hAll c P₀ A' val h
  obtain ⟨hM, -, -⟩ := hn₀ n₀ le_rfl
  obtain ⟨M, q, hf, hc⟩ := (boundInMForEveryMachine c P₀ A' val h.1).1
  obtain ⟨C, hC⟩ := hM M q hc
  exact ⟨M, C, hf, hC⟩
end NamesInOrder
