-- Prove2me | solution 1 for GeneralPieces.LemQ.sum_lst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:41:28.136555+00:00
-- url     : https://prove2.me/submissions/826b1b1b-b15e-4847-a05d-80c5900a34ee

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_GeneralPieces_LemQ_coe_lst

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.LemQ
theorem _root_.solution (μ : Ptn) : (lst μ).sum = wt μ := by
  rw [← Multiset.sum_coe, coe_lst]
  rfl
end GeneralPieces.LemQ
