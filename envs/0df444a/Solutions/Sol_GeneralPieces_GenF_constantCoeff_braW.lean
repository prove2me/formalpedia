-- Prove2me | solution 1 for GeneralPieces.GenF.constantCoeff_braW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:37:24.637027+00:00
-- url     : https://prove2.me/submissions/0d8fbd32-d808-4123-81de-113c5dd23d30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution (σ : Multiset ℕ) (w : W) : MvPowerSeries.constantCoeff (braW σ w) = bra σ (MvPowerSeries.constantCoeff w) := rfl
end GeneralPieces.GenF
