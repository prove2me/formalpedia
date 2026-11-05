-- Prove2me | solution 1 for GeneralPieces.GenF.coeff_lin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:26:16.015527+00:00
-- url     : https://prove2.me/submissions/4bc33c7f-b99f-4759-811f-570789aae617

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
omit [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution (b : X → A) (α : X →₀ ℕ) : coeff α (lin b) = if α.degree = 1 then ∑ v ∈ α.support, b v else 0 := rfl
end GeneralPieces.GenF
