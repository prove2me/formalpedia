-- Prove2me | solution 1 for GeneralPieces.LemQ.tri_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:12:28.499752+00:00
-- url     : https://prove2.me/submissions/afe05b3c-7551-4e9e-a24b-9480fde23c9a

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
theorem _root_.solution (hOp : OpFacts) (h : ℕ) : Tri fun a b f => pairing h a b • f where
  add₁ a a' b f := by rw [pairing, hOp.add_left, coeff_add, add_smul]; rfl
  smul₁ q a b f := by rw [pairing, hOp.smul_left, coeff_smul, smul_eq_mul, mul_smul]; rfl
  add₂ a b b' f := by rw [pairing, hOp.add_right, coeff_add, add_smul]; rfl
  smul₂ q a b f := by rw [pairing, hOp.smul_right, coeff_smul, smul_eq_mul, mul_smul]; rfl
  add₃ a b f f' := smul_add _ _ _
  smul₃ q a b f := smul_comm _ _ _
end GeneralPieces.LemQ
