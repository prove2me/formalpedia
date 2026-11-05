-- Prove2me | solution 2 for GeneralPieces.LemQ.tri_Q
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T00:36:43.517461+00:00
-- url     : https://prove2.me/submissions/eaf7178d-e2bf-4113-bb39-a7c2607a4ee6

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

theorem solution (hOp : OpFacts) (h : ℕ) (s : ℤ) : Tri (Q h s) :=
  Tri.sum _ fun i => (tri_ab hOp h i _ _).smul _
