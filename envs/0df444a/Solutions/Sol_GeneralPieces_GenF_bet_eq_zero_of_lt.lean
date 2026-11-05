-- Prove2me | solution 1 for GeneralPieces.GenF.bet_eq_zero_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:49:57.005889+00:00
-- url     : https://prove2.me/submissions/d236a853-a053-4ec3-a325-b92c9d475fb9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
import Theorems.Thm_ClauseBound_Boson_Scalars_choose_eq_zero


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution {n l : ℕ} (h : l < n) : bet n (l : ℤ) = 0 := by
  unfold bet
  split_ifs with h0
  · rfl
  · exact ClauseBound.Boson.Scalars.choose_eq_zero (by omega) (by omega)
end GeneralPieces.GenF
