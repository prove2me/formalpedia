-- Prove2me | solution 1 for GeneralPieces.GenF.coeff_expW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:24:56.029453+00:00
-- url     : https://prove2.me/submissions/37dc3735-c2a8-4598-bc07-40cb0486c26d

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
import Theorems.Thm_GeneralPieces_GenF_coeff_rat_smul
import Theorems.Thm_GeneralPieces_GenF_coeff_pow_eq_zero

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X R : Type} [CommRing R] [Algebra ℚ R]
namespace GeneralPieces.GenF
theorem _root_.solution {w : MvPowerSeries X R} (hw : constantCoeff w = 0) {α : X →₀ ℕ} {N : ℕ} (h : α.degree < N) : coeff α (expW w) = coeff α (expN N w) := by
  rw [coeff_expW_def]
  unfold expN
  rw [map_sum, map_sum]
  refine sum_subset (range_subset_range.2 (by omega)) fun n _ hn => ?_
  rw [coeff_rat_smul, coeff_pow_eq_zero hw (by simpa using hn), smul_zero]
end GeneralPieces.GenF
