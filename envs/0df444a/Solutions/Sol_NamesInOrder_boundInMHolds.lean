-- Prove2me | solution 1 for NamesInOrder.boundInMHolds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:26:14.619909+00:00
-- url     : https://prove2.me/submissions/51ff8ecb-cb4e-4216-b280-fc7eb71414cf

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
import Theorems.Thm_NamesInOrder_forAllPieces
import Theorems.Thm_NamesInOrder_boundInMHolds_of


set_option autoImplicit false
section
section
open NamesInOrder
open MainRoute PairsToBound
namespace NamesInOrder
theorem _root_.solution : BoundInMHolds := boundInMHolds_of forAllPieces
end NamesInOrder
