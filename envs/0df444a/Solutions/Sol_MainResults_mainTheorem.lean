-- Prove2me | solution 1 for MainResults.mainTheorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:03:41.464453+00:00
-- url     : https://prove2.me/submissions/545a887a-bf45-450e-9177-856e13848099

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainResults
import Definitions.Def_CountedRoute_Main
import Definitions.Def_NamesInOrder_Main
import Definitions.Def_Wrap_Main
import Definitions.Def_Eth_16a5ce4_Solution_Definitions
import Theorems.Thm_CountedRoute_mainTheoremHolds
import Theorems.Thm_NamesInOrder_mainTheoremHolds


set_option autoImplicit false

namespace MainResults
theorem _root_.solution : MainResults.MainTheorem := CountedRoute.mainTheoremHolds
end MainResults
