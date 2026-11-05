-- Prove2me | solution 1 for GeneralPieces.Series.dv_eps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:36:58.391117+00:00
-- url     : https://prove2.me/submissions/b4b9da9c-7dad-4220-99cf-38bf54534065

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
import Theorems.Thm_GeneralPieces_Series_dv_sub
import Theorems.Thm_GeneralPieces_Series_eps_mul_sub

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
namespace GeneralPieces.Series
theorem _root_.solution : dv eps = eps ^ 2 := by
  rw [dv.leibniz_of_mul_eq_one eps_mul_sub, dv_sub, smul_eq_mul]
  ring
end GeneralPieces.Series
