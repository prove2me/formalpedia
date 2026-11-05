-- Prove2me | solution 1 for GeneralPieces.Sizes.coef_op
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:30:18.498649+00:00
-- url     : https://prove2.me/submissions/d5373778-062a-4dff-b015-c4d1115e4fb1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_ClauseBound_Boson_Text_coef_smul
import Theorems.Thm_GeneralPieces_Ring_coef_smul
import Theorems.Thm_GeneralPieces_Ring_coef_sum


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution (a : V) (r : ℤ) (σ' σ : Ptn) :
    coef σ' (op a r (tpow σ)) = ∑ m ∈ a.support, coeff m a * coef σ' (opMon (Finsupp.toMultiset m).toList r (tpow σ)) := by
  unfold op
  rw [coef_sum]
  exact sum_congr rfl fun m _ => coef_smul _ _ _
end GeneralPieces.Sizes
