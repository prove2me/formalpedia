-- Prove2me | solution 1 for GeneralPieces.GenF.lin1_tT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:48:55.72004+00:00
-- url     : https://prove2.me/submissions/dfae810a-309a-4932-9571-e867b9804731

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_GeneralPieces_GenF_degree_of_coeff_C_mul_X

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution (k : ℕ) : Lin1 (tT k) := fun y m h => by
  unfold tT at h
  rw [HahnSeries.C_apply, HahnSeries.coeff_single] at h
  split_ifs at h
  · refine degree_of_coeff_C_mul_X (c := 1) (k := k) ?_
    rwa [map_one, one_mul]
  · exact absurd (MvPolynomial.coeff_zero m) h
end GeneralPieces.GenF
