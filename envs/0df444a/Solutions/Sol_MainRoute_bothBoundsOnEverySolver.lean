-- Prove2me | solution 1 for MainRoute.bothBoundsOnEverySolver
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:46:48.710262+00:00
-- url     : https://prove2.me/submissions/a4a20cfc-4ff0-4ff2-bc5d-f1ca566eb880

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
import Theorems.Thm_MainRoute_routeOnEverySolver
import Theorems.Thm_MainRoute_bothBounds_of
import Theorems.Thm_MainRoute_boundInMOnEverySolver


set_option autoImplicit false
section
section
open MainRoute
open MinOfBounds PairsToBound
namespace MainRoute
theorem _root_.solution : BothBoundsOnEverySolver := bothBounds_of routeOnEverySolver boundInMOnEverySolver
end MainRoute
