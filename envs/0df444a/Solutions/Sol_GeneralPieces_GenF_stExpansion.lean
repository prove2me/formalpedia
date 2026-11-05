-- Prove2me | solution 1 for GeneralPieces.GenF.stExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:43:49.616716+00:00
-- url     : https://prove2.me/submissions/f9f1cfcb-0052-4adc-bc03-629e6bc1d5c7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Commute
import Definitions.Def_GeneralPieces_GenF_Normal
import Definitions.Def_GeneralPieces_GenF_YMain
import Definitions.Def_GeneralPieces_GenF_Assemble
import Definitions.Def_GeneralPieces_Series_LemmaQ
import Definitions.Def_GeneralPieces_GenF_Main
import Theorems.Thm_GeneralPieces_GenF_stN1
import Theorems.Thm_GeneralPieces_GenF_stN2
import Theorems.Thm_GeneralPieces_GenF_stN3
import Theorems.Thm_GeneralPieces_GenF_stNeq
import Theorems.Thm_GeneralPieces_GenF_stTwoOrders
import Theorems.Thm_GeneralPieces_GenF_stY
import Theorems.Thm_GeneralPieces_stExpansion_of


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
namespace GeneralPieces.GenF
theorem _root_.solution : GeneralPieces.Series.StExpansion := GeneralPieces.stExpansion_of stTwoOrders (stN1 stNeq) stN2 (stN3 stNeq) stY
end GeneralPieces.GenF
