-- Prove2me | solution 1 for GeneralPieces.GenF.Normal.C_rat_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:37:33.932058+00:00
-- url     : https://prove2.me/submissions/20ee3af5-789f-4a68-bd4d-2f93e72b5b62

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
variable {Y A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
namespace Normal
theorem _root_.solution (q : ℚ) (a : A) : MvPowerSeries.C (σ := Y) (q • a) = q • MvPowerSeries.C (σ := Y) a :=
  map_rat_smul (MvPowerSeries.C (σ := Y) (R := A)) q a
end Normal
end GeneralPieces.GenF
