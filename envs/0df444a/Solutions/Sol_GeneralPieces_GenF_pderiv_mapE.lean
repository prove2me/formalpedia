-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_mapE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:26:44.928616+00:00
-- url     : https://prove2.me/submissions/8f495a35-0dda-45ea-b2e8-aaa365575946

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Taylor
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Definitions.Def_GeneralPieces_GenF_PDeriv

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution (D : A →ₗ[ℚ] A) (i : X) (f : MvPowerSeries X A) : pderiv A i (mapE D f) = mapE D (pderiv A i f) := by
  ext α
  rw [coeff_pderiv, coeff_mapE, coeff_mapE, coeff_pderiv]
  have h : ∀ c : A, c * ((α i : A) + 1) = (α i + 1) • c := fun c => by rw [nsmul_eq_mul]; push_cast; ring
  rw [h, h, map_nsmul]
end GeneralPieces.GenF
