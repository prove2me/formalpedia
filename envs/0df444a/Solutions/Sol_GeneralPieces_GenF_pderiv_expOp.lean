-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_expOp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:49:47.328518+00:00
-- url     : https://prove2.me/submissions/4e7b90b2-a12b-4651-801d-a36e6072cdf3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Taylor
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Definitions.Def_GeneralPieces_GenF_PDeriv
import Theorems.Thm_GeneralPieces_GenF_degree_add_single
import Theorems.Thm_GeneralPieces_GenF_pderiv_opN

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution {O : X → A →ₗ[ℚ] A} (hc : ∀ v v' a, O v (O v' a) = O v' (O v a)) (i : X) (f : MvPowerSeries X A) :
    pderiv A i (expOp O f) = expOp O (pderiv A i f) + expOp O (mapE (O i) f) := by
  ext α
  rw [coeff_pderiv, coeff_expOp O f (N := α.degree + 1 + 1) (by rw [degree_add_single]; omega), ← coeff_pderiv, pderiv_opN hc, map_add, map_add,
    ← coeff_expOp O _ (by omega), ← coeff_expOp O _ (by omega)]
end GeneralPieces.GenF
