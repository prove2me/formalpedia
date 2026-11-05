-- Prove2me | solution 1 for GeneralPieces.GenF.coeff_mul_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:02:13.665197+00:00
-- url     : https://prove2.me/submissions/2b96652e-7032-45d4-a454-ce9339aa0967

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
omit [Algebra ℚ R]
namespace GeneralPieces.GenF
theorem _root_.solution {f f' g g' : MvPowerSeries X R} {α : X →₀ ℕ} (hf : ∀ β : X →₀ ℕ, β.degree ≤ α.degree → coeff β f = coeff β f')
    (hg : ∀ β : X →₀ ℕ, β.degree ≤ α.degree → coeff β g = coeff β g') : coeff α (f * g) = coeff α (f' * g') := by
  classical
  rw [coeff_mul, coeff_mul]
  refine sum_congr rfl fun p hp => ?_
  have h := congrArg Finsupp.degree (mem_antidiagonal.1 hp)
  rw [map_add] at h
  rw [hf p.1 (by omega), hg p.2 (by omega)]
end GeneralPieces.GenF
