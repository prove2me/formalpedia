-- Prove2me | solution 1 for GeneralPieces.GenF.support_bra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:36:15.284563+00:00
-- url     : https://prove2.me/submissions/0e93a24c-c6ed-436d-9827-a4888dacc967

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
theorem _root_.solution (σ : Multiset ℕ) (f : Tv) : (bra σ f).support ⊆ f.support := fun y hy h => hy (by rw [coeff_bra, h, MvPolynomial.coeff_zero])
end GeneralPieces.GenF
