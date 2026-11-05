-- Prove2me | solution 1 for GeneralPieces.Ring.op_add_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:39:09.861607+00:00
-- url     : https://prove2.me/submissions/597111e0-140c-4aca-a059-3e1d6f7cd6f5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_opMon_add

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (a : V) (r : ℤ) (f g : V) : op a r (f + g) = op a r f + op a r g := by
  unfold op
  rw [← sum_add_distrib]
  exact sum_congr rfl fun m _ => by rw [opMon_add, smul_add]
end GeneralPieces.Ring
