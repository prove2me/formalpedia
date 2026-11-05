-- Prove2me | solution 1 for GeneralPieces.LemQ.tri_ab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:12:08.259841+00:00
-- url     : https://prove2.me/submissions/5d56667f-bfca-49bf-8a6e-ab009cd240b7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_GeneralPieces_LemQ_angle_add
import Theorems.Thm_GeneralPieces_LemQ_angle_smul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.LemQ
theorem _root_.solution (hOp : OpFacts) (h i : ℕ) (r r' : ℤ) : Tri fun a b f => op (angle h i a) r (op b r' f) where
  add₁ a a' b f := by rw [angle_add, hOp.add_left]
  smul₁ q a b f := by rw [angle_smul, hOp.smul_left]
  add₂ a b b' f := by rw [hOp.add_left, hOp.add_right]
  smul₂ q a b f := by rw [hOp.smul_left, hOp.smul_right]
  add₃ a b f f' := by rw [hOp.add_right, hOp.add_right]
  smul₃ q a b f := by rw [hOp.smul_right, hOp.smul_right]
end GeneralPieces.LemQ
