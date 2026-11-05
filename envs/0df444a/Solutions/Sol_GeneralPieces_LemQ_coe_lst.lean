-- Prove2me | solution 1 for GeneralPieces.LemQ.coe_lst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:40:00.863383+00:00
-- url     : https://prove2.me/submissions/361fbb20-290c-42a7-bd31-852025cc5a65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.LemQ
theorem _root_.solution (μ : Ptn) : (lst μ : Multiset ℕ) = toN μ := by
  unfold lst toL toN
  rw [← Multiset.map_coe, Multiset.coe_toList]
end GeneralPieces.LemQ
