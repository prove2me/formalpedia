-- Prove2me | solution 1 for GeneralPieces.GenF.degree_add_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:26:36.749515+00:00
-- url     : https://prove2.me/submissions/ccf714a3-cfeb-451b-a9d5-1d78578b75db

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
theorem _root_.solution (α : X →₀ ℕ) (i : X) : (α + Finsupp.single i 1).degree = α.degree + 1 := by
  rw [map_add, Finsupp.degree_single]
end GeneralPieces.GenF
