-- Prove2me | solution 1 for GeneralPieces.GenF.coeff_expW_of_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:43:56.344503+00:00
-- url     : https://prove2.me/submissions/07105937-6c5a-454a-b751-f7294f21bdd7

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
import Theorems.Thm_GeneralPieces_GenF_coeff_tw
import Theorems.Thm_GeneralPieces_GenF_expW_tw

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X R : Type} [CommRing R] [Algebra ℚ R]
namespace GeneralPieces.GenF
theorem _root_.solution (wt : (X →₀ ℕ) →+ ℕ) (ε : R) (q : MvPowerSeries X ℚ) {w : MvPowerSeries X R}
    (hw : ∀ α, coeff α w = algebraMap ℚ R (coeff α q) * ε ^ wt α) (α : X →₀ ℕ) : coeff α (expW w) = algebraMap ℚ R (coeff α (expW q)) * ε ^ wt α := by
  have h : w = tw wt ε q := by ext β; rw [hw, coeff_tw]
  rw [h, expW_tw, coeff_tw]
end GeneralPieces.GenF
