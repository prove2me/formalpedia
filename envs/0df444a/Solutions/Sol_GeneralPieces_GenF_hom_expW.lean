-- Prove2me | solution 1 for GeneralPieces.GenF.hom_expW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:50:41.006188+00:00
-- url     : https://prove2.me/submissions/ed15b4e4-5442-4539-8102-db34967e79af

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
import Theorems.Thm_GeneralPieces_GenF_coeff_expW
import Theorems.Thm_GeneralPieces_GenF_map_expN

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X R : Type} [CommRing R] [Algebra ℚ R]
namespace GeneralPieces.GenF
theorem _root_.solution (Φ : MvPowerSeries X R →+* MvPowerSeries X R)
    (hΦ : ∀ (α : X →₀ ℕ) (f g : MvPowerSeries X R), (∀ β : X →₀ ℕ, β.degree ≤ α.degree → coeff β f = coeff β g) → coeff α (Φ f) = coeff α (Φ g))
    {w : MvPowerSeries X R} (hw : constantCoeff w = 0) : Φ (expW w) = expW (Φ w) := by
  ext α
  rw [hΦ α (expW w) (expN (α.degree + 1) w) fun β hβ => coeff_expW hw (by omega), map_expN, coeff_expW_def]
end GeneralPieces.GenF
