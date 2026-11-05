-- Prove2me | solution 1 for GeneralPieces.GenF.coeff_smul_mo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:32:41.347651+00:00
-- url     : https://prove2.me/submissions/ec3d79fc-bfc2-485a-bd27-be0c4bed779a

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
theorem _root_.solution (q : ℚ) (x y y' : ℤ) : (q • mo x y).coeff y' = if y' = y then C q * T x else 0 := by
  unfold mo
  rw [HahnSeries.coeff_smul, HahnSeries.coeff_single]
  split_ifs
  · rw [← LaurentPolynomial.smul_eq_C_mul]
  · rw [smul_zero]
end GeneralPieces.GenF
