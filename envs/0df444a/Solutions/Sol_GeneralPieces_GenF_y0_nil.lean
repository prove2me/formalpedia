-- Prove2me | solution 1 for GeneralPieces.GenF.y0_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:00:52.12478+00:00
-- url     : https://prove2.me/submissions/64744774-b9f9-4edf-ad71-b022b4eaeb01

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
theorem _root_.solution (σ : Multiset ℕ) (p : Vu) : y0 [] σ p = MvPolynomial.coeff (Multiset.toFinsupp σ) p := rfl
end GeneralPieces.GenF
