-- Prove2me | solution 1 for GeneralPieces.GenF.Y.pderiv_rat_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:59:31.834122+00:00
-- url     : https://prove2.me/submissions/fc676f94-7807-4180-9a32-b0f44bd0b4c9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
open GeneralPieces.GenF.Y
variable {Z R : Type} [CommRing R] [Algebra ℚ R]
namespace GeneralPieces.GenF.Y
theorem _root_.solution (i : Z) (q : ℚ) (F : MvPowerSeries Z R) : pderiv R i (q • F) = q • pderiv R i F := map_rat_smul (pderiv R i).toLinearMap q F
end GeneralPieces.GenF.Y
