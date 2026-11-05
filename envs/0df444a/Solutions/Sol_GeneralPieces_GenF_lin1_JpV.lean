-- Prove2me | solution 1 for GeneralPieces.GenF.lin1_JpV
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:39:06.589928+00:00
-- url     : https://prove2.me/submissions/209e04ca-e1f0-4a4f-9b3b-aa9280adf4fc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_GeneralPieces_GenF_degree_of_coeff_C_mul_X
import Theorems.Thm_GeneralPieces_GenF_coeff_JpV

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution (n : ℕ) : Lin1 (JpV n) := fun y m h => by
  rw [coeff_JpV] at h
  split_ifs at h
  · exact degree_of_coeff_C_mul_X h
  · exact absurd (MvPolynomial.coeff_zero m) h
end GeneralPieces.GenF
