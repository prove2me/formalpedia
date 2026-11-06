-- Prove2me | solution 1 for NamesInOrder.forAllPieces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:19:18.332562+00:00
-- url     : https://prove2.me/submissions/fd4784ac-0f17-4daa-b8f1-3a315a56fd0f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NamesInOrder_Defs
import Definitions.Def_NamesInOrder_Arith
import Definitions.Def_NamesInOrder_Chain
import Definitions.Def_NamesInOrder_General
import Definitions.Def_MainRoute_GeneralMain
import Definitions.Def_PairsToBound_Main
import Definitions.Def_NamesInOrder_Main
import Theorems.Thm_NamesInOrder_onEverySolver
import Theorems.Thm_NamesInOrder_forAllPieces_of
import Theorems.Thm_PairsToBound_thePairsSatisfyTheHypothesis
import Theorems.Thm_PairsToBound_thetaOfThePairs


set_option autoImplicit false
section
section
open NamesInOrder
open MainRoute PairsToBound
namespace NamesInOrder
theorem _root_.solution : ForAllPieces := forAllPieces_of onEverySolver thePairsSatisfyTheHypothesis thetaOfThePairs
end NamesInOrder
