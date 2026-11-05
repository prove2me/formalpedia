-- Prove2me | solution 1 for GeneralPieces.Series.cfP_sumP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:35:26.623918+00:00
-- url     : https://prove2.me/submissions/34ab0324-f5dc-485a-8f1c-e4985fe83452

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
import Theorems.Thm_GeneralPieces_Series_cf_ser

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
namespace GeneralPieces.Series
theorem _root_.solution (j n : ℕ) (c : ℤ → ℚ) (x y : ℤ) : cfP (sumP j n c) x y = if 1 ≤ y + n ∧ x + y = -((j : ℤ) + n) then c (y + n) else 0 := cf_ser j n c x y
end GeneralPieces.Series
