-- Prove2me | solution 1 for GeneralPieces.GenF.Normal.mapD_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:54:54.678538+00:00
-- url     : https://prove2.me/submissions/277b60e9-1dee-41f6-b151-ea576f046e33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal
import Theorems.Thm_GeneralPieces_GenF_coeff_mapD


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
variable {Y A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
namespace Normal
theorem _root_.solution (d : Derivation ℚ A A) (a : A) : mapD (X := Y) d (MvPowerSeries.C a) = MvPowerSeries.C (d a) := by
  classical
  ext1 α
  rw [coeff_mapD, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  split_ifs
  · rfl
  · exact map_zero d
end Normal
end GeneralPieces.GenF
