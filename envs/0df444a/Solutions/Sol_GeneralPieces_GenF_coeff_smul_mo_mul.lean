-- Prove2me | solution 1 for GeneralPieces.GenF.coeff_smul_mo_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:02:48.135174+00:00
-- url     : https://prove2.me/submissions/274ef505-3a47-432e-90a4-d8ba0a7cc934

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_Eth_16a5ce4_GeneralPieces_GenF_Y2_Definitions

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset
namespace GeneralPieces.GenF
theorem _root_.solution (q : ℚ) (x : ℤ) (f : S) (y : ℤ) : ((q • mo x 0) * f).coeff y = (C q * T x) * f.coeff y := by
  rw [smul_mul_assoc, HahnSeries.coeff_smul, mo, HahnSeries.coeff_single_zero_mul, Algebra.smul_def, mul_assoc]
  rfl
end GeneralPieces.GenF
