-- Prove2me | solution 1 for GeneralPieces.GenF.Normal.emb_smul_mo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:56:45.22674+00:00
-- url     : https://prove2.me/submissions/17f697bb-e9ba-42e3-a791-afd634c509ef

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
namespace Normal
theorem _root_.solution (q : ℚ) (x : ℤ) : emb (q • mo x 0) = HahnSeries.C (MvPolynomial.C (C q * T x)) := by
  refine HahnSeries.ext (funext fun y => ?_)
  show MvPolynomial.C (q • (mo x 0).coeff y) = _
  rw [mo, HahnSeries.C_apply]
  by_cases h : y = 0
  · rw [h, HahnSeries.coeff_single_same, HahnSeries.coeff_single_same, LaurentPolynomial.smul_eq_C_mul]
  · rw [HahnSeries.coeff_single_of_ne h, HahnSeries.coeff_single_of_ne h, smul_zero, map_zero]
end Normal
end GeneralPieces.GenF
