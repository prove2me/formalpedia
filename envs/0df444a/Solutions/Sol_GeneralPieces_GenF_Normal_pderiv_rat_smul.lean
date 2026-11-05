-- Prove2me | solution 1 for GeneralPieces.GenF.Normal.pderiv_rat_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:55:07.105234+00:00
-- url     : https://prove2.me/submissions/885cddf3-16ea-47b3-b36c-fffd87654040

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
theorem _root_.solution (i : Y) (q : ℚ) (f : MvPowerSeries Y A) : MvPowerSeries.pderiv A i (q • f) = q • MvPowerSeries.pderiv A i f :=
  map_rat_smul (MvPowerSeries.pderiv A i).toLinearMap q f
end Normal
end GeneralPieces.GenF
