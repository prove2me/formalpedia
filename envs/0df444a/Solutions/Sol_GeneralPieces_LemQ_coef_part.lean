-- Prove2me | solution 1 for GeneralPieces.LemQ.coef_part
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:32:55.509277+00:00
-- url     : https://prove2.me/submissions/50c96a12-6638-4f2b-9940-95b07e35fa5d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_GeneralPieces_Ring_weight_toFinsupp


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.LemQ
theorem _root_.solution (π : Ptn) (h' : ℕ) (a : V) : coef π (part h' a) = if wt π = h' then coef π a else 0 := by
  unfold coef part
  rw [coeff_weightedHomogeneousComponent]
  have := weight_toFinsupp π
  unfold wgt at this
  rw [this]
end GeneralPieces.LemQ
