-- Prove2me | solution 1 for GeneralPieces.GenF.braW_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:51:12.719706+00:00
-- url     : https://prove2.me/submissions/f7c57b0d-0ba0-4588-a7ac-11bc7f4b2eb3

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
theorem _root_.solution (σ : Multiset ℕ) (q : ℚ) (w : W) : braW σ (q • w) = q • braW σ w := map_rat_smul (braWH σ) q w
end GeneralPieces.GenF
