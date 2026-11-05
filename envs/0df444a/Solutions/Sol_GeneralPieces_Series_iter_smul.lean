-- Prove2me | solution 1 for GeneralPieces.Series.iter_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:01:46.912473+00:00
-- url     : https://prove2.me/submissions/18a6f81e-0a42-4171-81d9-5364036183e5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
variable {A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.Series
theorem _root_.solution (D : Derivation ℚ A A) (a : ℕ) (r : ℚ) (z : A) : D^[a] (r • z) = r • D^[a] z := by
  induction a generalizing z with
  | zero => rfl
  | succ a ih => rw [Function.iterate_succ_apply, D.map_smul, ih, Function.iterate_succ_apply]
end GeneralPieces.Series
