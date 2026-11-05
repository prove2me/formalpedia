-- Prove2me | solution 1 for GeneralPieces.GenF.expOp_expW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:45:04.456135+00:00
-- url     : https://prove2.me/submissions/28c65475-fb90-46b5-83f4-5df9c24ee9d1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Exp
import Mathlib.Algebra.MvPolynomial.Derivation
import Definitions.Def_GeneralPieces_GenF_Taylor
import Theorems.Thm_GeneralPieces_GenF_coeff_expOp_congr
import Theorems.Thm_GeneralPieces_GenF_hom_expW


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution {O : X → A →ₗ[ℚ] A} (hO : ∀ v, IsDer (O v)) {w : MvPowerSeries X A} (hw : constantCoeff w = 0) : expOp O (expW w) = expW (expOp O w) :=
  hom_expW (expOpHom O hO) (coeff_expOp_congr O) hw
end GeneralPieces.GenF
