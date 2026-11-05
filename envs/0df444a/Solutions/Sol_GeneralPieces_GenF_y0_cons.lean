-- Prove2me | solution 1 for GeneralPieces.GenF.y0_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:39:08.692818+00:00
-- url     : https://prove2.me/submissions/2d19534c-86c8-4367-b6cc-054b473ae347

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
theorem _root_.solution (n : ℕ) (a : List ℕ) (σ : Multiset ℕ) (p : Vu) :
    y0 (n :: a) σ p = ∑ l ∈ σ.toFinset, (C (bet n l : ℚ) * T ((l : ℤ) - n)) * y0 a (σ.erase l) p + y0 a σ (JmU n p) := by
  show (∑ l ∈ σ.toFinset, (C (bet n l : ℚ) * T ((l : ℤ) - n)) • y0 a (σ.erase l) + (y0 a σ).comp (JmU n).toLinearMap) p = _
  rw [LinearMap.add_apply, LinearMap.sum_apply]
  rfl
end GeneralPieces.GenF
