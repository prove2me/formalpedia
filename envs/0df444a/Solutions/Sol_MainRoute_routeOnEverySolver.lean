-- Prove2me | solution 1 for MainRoute.routeOnEverySolver
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:39:16.298354+00:00
-- url     : https://prove2.me/submissions/ae8e7689-4852-4536-9611-f59f1cf5a9d5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainRoute_GeneralDefs
import Definitions.Def_MainRoute_General
import Definitions.Def_MainRoute_GeneralInM
import Definitions.Def_MinOfBounds_Main
import Definitions.Def_MinOfBounds_Rename
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_PairsToBound_Main
import Definitions.Def_RecursionToBound_Main
import Definitions.Def_MainRoute_GeneralMain
import Theorems.Thm_MainRoute_routeOn_of
import Theorems.Thm_MinOfBounds_everyAlternationDecidesWithinMinBound
import Theorems.Thm_MinOfBounds_everyAlternationMeetsMinBound
import Theorems.Thm_MinOfBounds_minBoundIsTheMainTheorem
import Theorems.Thm_MinOfBounds_renamingFrontEndExists
import Theorems.Thm_PairsToBound_everyChoiceMeetsThmVariablesB
import Theorems.Thm_PairsToBound_everyExhaustiveMachineTriesAll
import Theorems.Thm_PairsToBound_exhaustiveMachineExists
import Theorems.Thm_PairsToBound_frontEndAndTestExist
import Theorems.Thm_RecursionToBound_thmVariablesAForEveryMachine


set_option autoImplicit false
section
section
open MainRoute
open MinOfBounds PairsToBound
namespace MainRoute
theorem _root_.solution : RouteOnEverySolver :=
  routeOn_of RecursionToBound.thmVariablesAForEveryMachine everyChoiceMeetsThmVariablesB everyExhaustiveMachineTriesAll frontEndAndTestExist exhaustiveMachineExists
    everyAlternationMeetsMinBound everyAlternationDecidesWithinMinBound renamingFrontEndExists minBoundIsTheMainTheorem
end MainRoute
