-- Prove2me | solution 1 for GeneralPieces.Sizes.wt_erase_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:28:28.023014+00:00
-- url     : https://prove2.me/submissions/4ae258e1-89b1-486e-b55a-487663effd72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt
import Theorems.Thm_GeneralPieces_Ring_wt_erase


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution (σ : Ptn) (l : ℕ+) : wt (σ.erase l) ≤ wt σ := by
  by_cases hl : l ∈ σ
  · have := wt_erase hl
    omega
  · rw [Multiset.erase_of_notMem hl]
end GeneralPieces.Sizes
