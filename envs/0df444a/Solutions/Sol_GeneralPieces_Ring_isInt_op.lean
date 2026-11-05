-- Prove2me | solution 1 for GeneralPieces.Ring.isInt_op
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:45:09.236213+00:00
-- url     : https://prove2.me/submissions/33a4beee-5bd6-4260-86d6-4094177010fe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
import Theorems.Thm_GeneralPieces_Ring_isInt_sum
import Theorems.Thm_GeneralPieces_Ring_isInt_zsmul
import Theorems.Thm_GeneralPieces_Ring_isInt_opMon

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {a f : V} (ha : IsInt a) (hf : IsInt f) (r : ℤ) : IsInt (op a r f) :=
  isInt_sum _ _ fun m _ => by
    obtain ⟨z, hz⟩ := ha m
    rw [hz]
    exact isInt_zsmul (isInt_opMon hf _ r) z
end GeneralPieces.Ring
