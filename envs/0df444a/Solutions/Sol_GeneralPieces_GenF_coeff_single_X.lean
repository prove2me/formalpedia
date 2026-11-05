-- Prove2me | solution 1 for GeneralPieces.GenF.coeff_single_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:31:51.190733+00:00
-- url     : https://prove2.me/submissions/2b3cfa5c-0079-4d5d-839f-396f1707bd4d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution (l k : ℕ) : MvPolynomial.coeff (Finsupp.single l 1) (MvPolynomial.X k : Vu) = if l = k then 1 else 0 := by
  classical
  rw [MvPolynomial.coeff_X]
  by_cases h : l = k
  · rw [if_pos h, h, if_pos rfl]
  · rw [if_neg h, if_neg fun e => h (Finsupp.single_left_injective one_ne_zero e).symm]
end GeneralPieces.GenF
