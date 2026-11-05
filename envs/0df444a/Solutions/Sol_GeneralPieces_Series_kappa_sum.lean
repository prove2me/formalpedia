-- Prove2me | solution 1 for GeneralPieces.Series.kappa_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:42:22.272676+00:00
-- url     : https://prove2.me/submissions/bdb5a762-13b7-45e7-b820-f11bb0d8a281

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
import Theorems.Thm_GeneralPieces_Series_displayGamma_P
import Theorems.Thm_GeneralPieces_Series_leftGamma_P

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
namespace GeneralPieces.Series
theorem _root_.solution {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    (sumP j n fun k => (k : ℚ) * (Ring.choose (-k - 1) (j - 1) : ℤ) * (Ring.choose (k - 1) (n - 1) : ℤ)) = (ClauseBound.Boson.Gam j n : ℚ) • epsP ^ (j + n) := by
  rw [← leftGamma_P hj hn, displayGamma_P hj hn]
end GeneralPieces.Series
