-- Prove2me | solution 1 for GeneralPieces.GenF.bra_emb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:48:17.641762+00:00
-- url     : https://prove2.me/submissions/e32721a1-881f-439f-9650-a7438a9f9ad1

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
theorem _root_.solution (σ : Multiset ℕ) (s : S) : bra σ (emb s) = if σ = 0 then s else 0 := by
  classical
  ext y : 2
  rw [coeff_bra, coeff_emb, MvPolynomial.coeff_C]
  by_cases h : σ = 0
  · rw [if_pos h, h, map_zero, if_pos rfl]
  · rw [if_neg h, if_neg, HahnSeries.coeff_zero]
    intro h0
    exact h (Multiset.toFinsupp.injective (by rw [← h0, map_zero]))
end GeneralPieces.GenF
