-- Prove2me | solution 1 for GeneralPieces.GenF.expD_expW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:46:12.756574+00:00
-- url     : https://prove2.me/submissions/04c2148f-7d4a-41c0-95a5-225f70e496bd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Exp
import Mathlib.Algebra.MvPolynomial.Derivation
import Definitions.Def_GeneralPieces_GenF_Taylor
import Theorems.Thm_GeneralPieces_GenF_expOp_expW

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution (D : X → Derivation ℚ A A) {w : MvPowerSeries X A} (hw : constantCoeff w = 0) : expD D (expW w) = expW (expD D w) :=
  expOp_expW (fun i => isDer_derivation (D i)) hw
end GeneralPieces.GenF
