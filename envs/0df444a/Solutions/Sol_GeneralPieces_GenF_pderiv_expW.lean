-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_expW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:47:20.563728+00:00
-- url     : https://prove2.me/submissions/42255b2c-158e-458f-969c-b052a4c5b4c1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Taylor
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Definitions.Def_GeneralPieces_GenF_PDeriv
import Theorems.Thm_GeneralPieces_GenF_degree_add_single
import Theorems.Thm_GeneralPieces_GenF_pderiv_expN
import Theorems.Thm_GeneralPieces_GenF_coeff_expW
import Theorems.Thm_GeneralPieces_GenF_coeff_mul_congr


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution (i : X) {w : MvPowerSeries X A} (hw : constantCoeff w = 0) : pderiv A i (expW w) = pderiv A i w * expW w := by
  ext α
  rw [coeff_pderiv, coeff_expW hw (N := α.degree + 1 + 1) (by rw [degree_add_single]; omega), ← coeff_pderiv, pderiv_expN]
  exact coeff_mul_congr (fun _ _ => rfl) fun β hβ => (coeff_expW hw (by omega)).symm
end GeneralPieces.GenF
