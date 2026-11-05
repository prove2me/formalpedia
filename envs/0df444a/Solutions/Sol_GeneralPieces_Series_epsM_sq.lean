-- Prove2me | solution 1 for GeneralPieces.Series.epsM_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:50:22.40479+00:00
-- url     : https://prove2.me/submissions/30d34f0b-9762-4e2b-94a5-de7778783348

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
import Theorems.Thm_GeneralPieces_Series_d1M_epsM
import Theorems.Thm_GeneralPieces_Series_dv_eps_eq

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
namespace GeneralPieces.Series
theorem _root_.solution : epsM ^ 2 = -d1M epsM ∧ -d1M epsM = sumM 1 1 fun k => (k : ℚ) :=
  ⟨by rw [d1M_epsM, neg_neg], by rw [epsM, d1M, map_neg, neg_neg]; exact dv_eps_eq⟩
end GeneralPieces.Series
