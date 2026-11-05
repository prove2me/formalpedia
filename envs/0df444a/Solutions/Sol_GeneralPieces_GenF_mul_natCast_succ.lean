-- Prove2me | solution 1 for GeneralPieces.GenF.mul_natCast_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:27:14.193955+00:00
-- url     : https://prove2.me/submissions/a3acb3f0-e5a2-4a0c-8713-ff800db200d6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_PDeriv
import Mathlib.Data.Finsupp.Multiset
import Definitions.Def_GeneralPieces_GenF_Coeff

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution (a : A) (n : ℕ) : a * ((n : A) + 1) = ((n : ℚ) + 1) • a := by
  rw [Algebra.smul_def, map_add, map_natCast, map_one, mul_comm]
end GeneralPieces.GenF
