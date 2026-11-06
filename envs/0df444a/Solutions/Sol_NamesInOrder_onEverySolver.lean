-- Prove2me | solution 1 for NamesInOrder.onEverySolver
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:01:55.927496+00:00
-- url     : https://prove2.me/submissions/f3aca0b0-591f-4e93-9c79-bbef39458139

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
import Theorems.Thm_NamesInOrder_everyDirectAlternationMeetsTheBound
import Theorems.Thm_MainRoute_bothBoundsOnEverySolver
import Theorems.Thm_NamesInOrder_boundInMWithoutThePolynomial
import Theorems.Thm_NamesInOrder_onEverySolver_of


set_option autoImplicit false
section
section
open NamesInOrder
open MainRoute PairsToBound
namespace NamesInOrder
theorem _root_.solution : OnEverySolver := onEverySolver_of bothBoundsOnEverySolver boundInMWithoutThePolynomial everyDirectAlternationMeetsTheBound
end NamesInOrder
