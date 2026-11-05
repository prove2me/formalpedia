-- Prove2me | solution 1 for GeneralPieces.Series.displayGamma_M
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:50:18.600119+00:00
-- url     : https://prove2.me/submissions/906a7940-5b82-4978-8bdc-857c12a85d18

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
import Theorems.Thm_GeneralPieces_Series_d1M_epsM
import Theorems.Thm_GeneralPieces_Series_d2M_epsM
import Theorems.Thm_GeneralPieces_Series_displayGamma

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
namespace GeneralPieces.Series
theorem _root_.solution {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    (1 / (((j - 1).factorial : ℚ) * ((n - 1).factorial : ℚ))) • d1M^[j - 1] (d2M^[n - 1] (epsM ^ 2)) = (ClauseBound.Boson.Gam j n : ℚ) • epsM ^ (j + n) :=
  displayGamma d1M d2M d1M_epsM d2M_epsM hj hn
end GeneralPieces.Series
