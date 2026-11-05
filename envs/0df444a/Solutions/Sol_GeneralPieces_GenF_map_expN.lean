-- Prove2me | solution 1 for GeneralPieces.GenF.map_expN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:02:26.905721+00:00
-- url     : https://prove2.me/submissions/d9ba7b40-d468-42bf-af4d-dda7b67fae48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralPieces_GenF_Exp

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X R : Type} [CommRing R] [Algebra ℚ R]
namespace GeneralPieces.GenF
theorem _root_.solution {Y R' : Type} [CommRing R'] [Algebra ℚ R'] (Φ : MvPowerSeries X R →+* MvPowerSeries Y R') (N : ℕ) (w : MvPowerSeries X R) :
    Φ (expN N w) = expN N (Φ w) := by
  unfold expN
  rw [map_sum]
  exact sum_congr rfl fun n _ => by rw [map_rat_smul, map_pow]
end GeneralPieces.GenF
