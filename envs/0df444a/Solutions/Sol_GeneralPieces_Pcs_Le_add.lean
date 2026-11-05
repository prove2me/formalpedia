-- Prove2me | solution 1 for GeneralPieces.Pcs.Le.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:24:06.962009+00:00
-- url     : https://prove2.me/submissions/252680ad-f21f-44d7-8915-399ef8d1dfa9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_GeneralPieces_LemQ_coef_add


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
namespace Le
theorem _root_.solution {h : ℕ} {a a' : V} (ha : Le h a) (ha' : Le h a') : Le h (a + a') := fun π hπ => by
  by_cases h1 : coef π a = 0
  · exact ha' π (by rwa [coef_add, h1, zero_add] at hπ)
  · exact ha π h1
end Le
end GeneralPieces.Pcs
