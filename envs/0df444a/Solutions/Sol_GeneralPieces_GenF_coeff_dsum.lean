-- Prove2me | solution 1 for GeneralPieces.GenF.coeff_dsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:45:10.368306+00:00
-- url     : https://prove2.me/submissions/776b7df5-7fec-474c-99b9-099e9c337740

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Exp
import Mathlib.Algebra.MvPolynomial.Derivation
import Definitions.Def_GeneralPieces_GenF_Taylor

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution (D : X → Derivation ℚ A A) (f : MvPowerSeries X A) (α : X →₀ ℕ) :
    coeff α (dsum D f) = ∑ i ∈ α.support, D i (coeff (α - Finsupp.single i 1) f) := rfl
end GeneralPieces.GenF
