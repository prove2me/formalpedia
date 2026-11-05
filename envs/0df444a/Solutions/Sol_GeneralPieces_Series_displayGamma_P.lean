-- Prove2me | solution 1 for GeneralPieces.Series.displayGamma_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:49:08.975282+00:00
-- url     : https://prove2.me/submissions/a45fce10-bedd-48d1-8d31-867e226426af

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
import Theorems.Thm_GeneralPieces_Series_d1P_epsP
import Theorems.Thm_GeneralPieces_Series_d2P_epsP
import Theorems.Thm_GeneralPieces_Series_displayGamma

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
namespace GeneralPieces.Series
theorem _root_.solution {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    (1 / (((j - 1).factorial : ℚ) * ((n - 1).factorial : ℚ))) • d1P^[j - 1] (d2P^[n - 1] (epsP ^ 2)) = (ClauseBound.Boson.Gam j n : ℚ) • epsP ^ (j + n) :=
  displayGamma d1P d2P d1P_epsP d2P_epsP hj hn
end GeneralPieces.Series
