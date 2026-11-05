-- Prove2me | solution 1 for GeneralPieces.GenF.Y.C_rat_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:38:49.091198+00:00
-- url     : https://prove2.me/submissions/2897d18c-83d7-467f-a2d1-45ab6c84894c

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
theorem _root_.solution (q : ℚ) (r : R) : (C (q • r) : MvPowerSeries Z R) = q • C r := map_rat_smul (C (σ := Z) (R := R)) q r
end GeneralPieces.GenF.Y
