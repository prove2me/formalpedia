-- Prove2me | solution 1 for GeneralPieces.GenF.stXo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:42.509051+00:00
-- url     : https://prove2.me/submissions/0959e243-8a7a-4dc6-ae87-4dfbee21bb31

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Y
import Definitions.Def_Eth_16a5ce4_GeneralPieces_GenF_Y2_Definitions
import Definitions.Def_GeneralPieces_GenF_YY
import Definitions.Def_GeneralPieces_GenF_YMain
import Theorems.Thm_GeneralPieces_GenF_Y2
import Theorems.Thm_GeneralPieces_GenF_pdL_GG_xo


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
namespace GeneralPieces.GenF
theorem _root_.solution : StXo := fun rd E σ b w => pdL_GG_xo rd E σ b w
end GeneralPieces.GenF
