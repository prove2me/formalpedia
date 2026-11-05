-- Prove2me | solution 1 for GeneralPieces.GenF.inv_factorial_succ_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:26:43.853495+00:00
-- url     : https://prove2.me/submissions/7844ace3-9639-425d-8c74-8b5e911ddc20

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
theorem _root_.solution (n : ℕ) : (((n + 1).factorial : ℚ)⁻¹) * ((n + 1 : ℕ) : ℚ) = ((n.factorial : ℚ)⁻¹) := by
  have h1 : (n.factorial : ℚ) ≠ 0 := by positivity
  rw [Nat.factorial_succ]
  push_cast
  have h2 : ((n : ℚ) + 1) ≠ 0 := by positivity
  field_simp
end GeneralPieces.GenF
