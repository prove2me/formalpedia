-- Prove2me | solution 1 for NamesInOrder.builtIsAssembledDirectly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:34:25.319941+00:00
-- url     : https://prove2.me/submissions/6f9b764e-43f4-41f1-8b71-195b700881e0

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

set_option autoImplicit false
section
section
open NamesInOrder
open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound MainRoute
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution : BuiltIsAssembledDirectly := by
  rintro fa ea fm em K₀ N ⟨Ma, Mb, M₂, M₁, qa, qb, q₂, -, q₁, q, -, pre, test, -, -, -, -, -, -, -, -, hfN, -, -, hMa, hMb, hpre, htest, -, hch, hM₁, -, halt⟩
  exact ⟨⟨M₁, M₂, q₁, q, ⟨Ma, Mb, qa, qb, q₂, pre, test, hMa, hMb, hpre, htest, hch⟩, hM₁, halt⟩, hfN⟩
end NamesInOrder
