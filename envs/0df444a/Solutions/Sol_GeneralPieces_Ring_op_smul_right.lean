-- Prove2me | solution 1 for GeneralPieces.Ring.op_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:39:07.393075+00:00
-- url     : https://prove2.me/submissions/1e8b0cbf-d2cf-4ff0-8f48-b37ba76d61d1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_opMon_smul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (a : V) (r : ℤ) (q : ℚ) (f : V) : op a r (q • f) = q • op a r f := by
  unfold op
  rw [smul_sum]
  exact sum_congr rfl fun m _ => by rw [opMon_smul, smul_comm]
end GeneralPieces.Ring
