-- Prove2me | solution 1 for GeneralPieces.Sizes.wt_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:29:43.215338+00:00
-- url     : https://prove2.me/submissions/da195d57-e1e4-429d-9a57-7a8929d29870

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution (n : ℕ+) (μ : Ptn) : wt (n ::ₘ μ) = n + wt μ := by
  unfold wt
  rw [Multiset.map_cons, Multiset.sum_cons]
end GeneralPieces.Sizes
