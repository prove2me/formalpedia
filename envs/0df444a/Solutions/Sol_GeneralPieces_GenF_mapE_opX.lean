-- Prove2me | solution 1 for GeneralPieces.GenF.mapE_opX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:46:48.562349+00:00
-- url     : https://prove2.me/submissions/7f1e5252-7aa7-406d-8399-f5f11c41970e

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
theorem _root_.solution {O : X → A →ₗ[ℚ] A} (hc : ∀ v v' a, O v (O v' a) = O v' (O v a)) (i : X) (f : MvPowerSeries X A) : mapE (O i) (opX O f) = opX O (mapE (O i) f) := by
  ext α
  rw [coeff_mapE, coeff_opX, coeff_opX, map_sum]
  exact sum_congr rfl fun v _ => by rw [hc, coeff_mapE]
end GeneralPieces.GenF
