-- Prove2me | solution 1 for GeneralPieces.Ring.op_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:44:34.64388+00:00
-- url     : https://prove2.me/submissions/a55d99bd-8027-4481-b728-66c489342d45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
import Theorems.Thm_GeneralPieces_Ring_opMon_nil
import Theorems.Thm_GeneralPieces_Ring_op_tpow


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (r : ℤ) (f : V) : op 1 r f = if r = 0 then f else 0 := by
  have h : (1 : V) = tpow (([] : List ℕ+) : Multiset ℕ+) := by simp [tpow]
  rw [h, op_tpow, opMon_nil]
end GeneralPieces.Ring
