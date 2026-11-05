-- Prove2me | solution 1 for GeneralPieces.GenF.map_expW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:37:38.018272+00:00
-- url     : https://prove2.me/submissions/2a8e8f75-33e9-4d13-ae51-47250f4393ff

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
import Theorems.Thm_GeneralPieces_GenF_coeff_expW_def
import Theorems.Thm_GeneralPieces_GenF_map_expN

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X R : Type} [CommRing R] [Algebra ℚ R]
namespace GeneralPieces.GenF
theorem _root_.solution {R' : Type} [CommRing R'] [Algebra ℚ R'] (φ : R →+* R') (w : MvPowerSeries X R) : map φ (expW w) = expW (map φ w) := by
  ext α
  rw [coeff_map, coeff_expW_def, coeff_expW_def, ← map_expN, coeff_map]
end GeneralPieces.GenF
