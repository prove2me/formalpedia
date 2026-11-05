-- Prove2me | solution 1 for GeneralPieces.Pcs.wt_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:24:15.528692+00:00
-- url     : https://prove2.me/submissions/be565bdc-6e6a-4bb7-a5d2-dd92bc89b6d0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
theorem _root_.solution (μ ν : Ptn) : wt (μ + ν) = wt μ + wt ν := by
  unfold wt
  rw [Multiset.map_add, Multiset.sum_add]
end GeneralPieces.Pcs
