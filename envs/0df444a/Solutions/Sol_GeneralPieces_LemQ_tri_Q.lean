-- Prove2me | solution 1 for GeneralPieces.LemQ.tri_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:13:51.250929+00:00
-- url     : https://prove2.me/submissions/6adb6473-eb49-499a-9212-8e9f3a2e7484

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_GeneralPieces_LemQ_Tri_smul
import Theorems.Thm_GeneralPieces_LemQ_tri_ab

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.LemQ
theorem _root_.solution (hOp : OpFacts) (h : ℕ) (s : ℤ) : Tri (Q h s) := Tri.sum _ fun i => (tri_ab hOp h i _ _).smul _
end GeneralPieces.LemQ
