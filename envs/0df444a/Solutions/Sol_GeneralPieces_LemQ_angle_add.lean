-- Prove2me | solution 1 for GeneralPieces.LemQ.angle_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:39:14.698291+00:00
-- url     : https://prove2.me/submissions/ea2b214f-ea81-4cb3-a3af-f27ccfe436eb

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
theorem _root_.solution (h i : ℕ) (a a' : V) : angle h i (a + a') = angle h i a + angle h i a' := by
  unfold angle part
  simp only [map_add, smul_add, sum_add_distrib]
end GeneralPieces.LemQ
