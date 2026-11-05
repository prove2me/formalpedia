-- Prove2me | solution 1 for GeneralPieces.GenF.stY2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:41.468558+00:00
-- url     : https://prove2.me/submissions/8c9801ae-b9de-4535-9a49-7084897cc6bb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Y
import Definitions.Def_Eth_16a5ce4_GeneralPieces_GenF_Y2_Definitions
import Definitions.Def_GeneralPieces_GenF_YY
import Definitions.Def_GeneralPieces_GenF_YMain
import Theorems.Thm_GeneralPieces_GenF_Y2
import Theorems.Thm_GeneralPieces_GenF_y0_monomial


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
namespace GeneralPieces.GenF
theorem _root_.solution : StY2 := fun rd E a σ ha hE => ⟨y0 a σ, y0_monomial a σ, fun w hw => Y2 rd E a ha σ w hE hw⟩
end GeneralPieces.GenF
