-- Prove2me | solution 1 for GeneralPieces.Series.du_eps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:36:39.308196+00:00
-- url     : https://prove2.me/submissions/9c09af65-4fb5-4b2d-8661-a69eae249871

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
import Theorems.Thm_GeneralPieces_Series_du_sub
import Theorems.Thm_GeneralPieces_Series_eps_mul_sub

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
namespace GeneralPieces.Series
theorem _root_.solution : du eps = -eps ^ 2 := by
  rw [du.leibniz_of_mul_eq_one eps_mul_sub, du_sub, smul_eq_mul, mul_one]
end GeneralPieces.Series
