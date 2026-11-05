-- Prove2me | solution 1 for GeneralPieces.GenF.lin1_JpU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:50:09.246383+00:00
-- url     : https://prove2.me/submissions/81276ee3-d6fa-4835-b305-f2cb8f0ea441

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
theorem _root_.solution (E n : ℕ) : Lin1 (HahnSeries.C (JpU E n)) := fun y m h => by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single] at h
  split_ifs at h
  · unfold JpU at h
    rw [MvPolynomial.coeff_sum] at h
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact degree_of_coeff_C_mul_X hl
  · exact absurd (MvPolynomial.coeff_zero m) h
end GeneralPieces.GenF
