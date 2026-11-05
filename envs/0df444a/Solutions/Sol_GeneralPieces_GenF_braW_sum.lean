-- Prove2me | solution 1 for GeneralPieces.GenF.braW_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:51:08.173097+00:00
-- url     : https://prove2.me/submissions/aae7930f-49b3-4199-a585-93281b833730

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
theorem _root_.solution {ι : Type} (σ : Multiset ℕ) (s : Finset ι) (F : ι → W) : braW σ (∑ i ∈ s, F i) = ∑ i ∈ s, braW σ (F i) := map_sum (braWH σ) F s
end GeneralPieces.GenF
