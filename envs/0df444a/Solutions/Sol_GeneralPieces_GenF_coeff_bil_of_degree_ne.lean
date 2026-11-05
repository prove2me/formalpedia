-- Prove2me | solution 1 for GeneralPieces.GenF.coeff_bil_of_degree_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:48:03.29911+00:00
-- url     : https://prove2.me/submissions/a2015cc0-d744-4b38-964e-61b3cd513d84

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_GeneralPieces_GenF_coeff_bil

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
variable {R : Type}
namespace GeneralPieces.GenF
theorem _root_.solution [Semiring R] (q : X → X → R) {α : X →₀ ℕ} (h : α.degree ≠ 2) : MvPowerSeries.coeff α (bil q) = 0 := by
  rw [coeff_bil, if_neg h]
end GeneralPieces.GenF
