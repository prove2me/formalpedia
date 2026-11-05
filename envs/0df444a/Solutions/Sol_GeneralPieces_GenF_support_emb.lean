-- Prove2me | solution 1 for GeneralPieces.GenF.support_emb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:48:10.679533+00:00
-- url     : https://prove2.me/submissions/530785cb-8663-4065-9c4b-537677df85a3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_GeneralPieces_GenF_coeff_emb

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution (s : S) : (emb s).support ⊆ s.support := fun y hy h => hy (by rw [coeff_emb, h, map_zero])
end GeneralPieces.GenF
