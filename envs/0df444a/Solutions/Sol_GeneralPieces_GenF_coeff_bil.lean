-- Prove2me | solution 1 for GeneralPieces.GenF.coeff_bil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:36:14.307409+00:00
-- url     : https://prove2.me/submissions/65d86ee6-7678-4535-b02d-20d47381d245

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
variable {R : Type}
namespace GeneralPieces.GenF
theorem _root_.solution [Semiring R] (q : X → X → R) (α : X →₀ ℕ) :
    MvPowerSeries.coeff α (bil q) = if α.degree = 2 then ∑ i ∈ α.support, ∑ i' ∈ α.support, q i i' else 0 := rfl
end GeneralPieces.GenF
