-- Prove2me | solution 1 for GeneralPieces.GenF.expW_tw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:43:00.723861+00:00
-- url     : https://prove2.me/submissions/598b4dec-bb76-4d7d-8918-8ba9d2c910b9

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
import Theorems.Thm_GeneralPieces_GenF_coeff_tw

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X R : Type} [CommRing R] [Algebra ℚ R]
namespace GeneralPieces.GenF
theorem _root_.solution (wt : (X →₀ ℕ) →+ ℕ) (ε : R) (q : MvPowerSeries X ℚ) : expW (tw wt ε q) = tw wt ε (expW q) := by
  ext α
  rw [coeff_expW_def, ← map_expN, coeff_tw, coeff_tw, coeff_expW_def]
end GeneralPieces.GenF
