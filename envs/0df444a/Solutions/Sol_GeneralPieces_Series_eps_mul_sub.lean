-- Prove2me | solution 1 for GeneralPieces.Series.eps_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:25:42.721183+00:00
-- url     : https://prove2.me/submissions/52693fd7-986c-45d9-af7a-8bf8907a52cd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
import Theorems.Thm_GeneralPieces_Series_sub_mul_eps


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
namespace GeneralPieces.Series
theorem _root_.solution : eps * (mo 1 0 - mo 0 1) = 1 := by rw [mul_comm, sub_mul_eps]
end GeneralPieces.Series
