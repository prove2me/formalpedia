-- Prove2me | solution 1 for GeneralPieces.GenF.bra_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:36:16.348721+00:00
-- url     : https://prove2.me/submissions/fb62acb3-5923-4ff1-bdbf-1ae892abe540

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
theorem _root_.solution {ι : Type} (σ : Multiset ℕ) (s : Finset ι) (F : ι → Tv) : bra σ (∑ i ∈ s, F i) = ∑ i ∈ s, bra σ (F i) := map_sum (braH σ) F s
end GeneralPieces.GenF
