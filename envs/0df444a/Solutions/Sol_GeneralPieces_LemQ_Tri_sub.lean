-- Prove2me | solution 1 for GeneralPieces.LemQ.Tri.sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:11:33.682803+00:00
-- url     : https://prove2.me/submissions/6431cfe0-1139-4d64-bbf7-3406714deeeb

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
open GeneralPieces.LemQ.Tri
variable {T T' : V → V → V → V}
namespace GeneralPieces.LemQ.Tri
theorem _root_.solution (hT : Tri T) (hT' : Tri T') : Tri fun a b f => T a b f - T' a b f where
  add₁ a a' b f := by rw [hT.add₁, hT'.add₁]; abel
  smul₁ q a b f := by rw [hT.smul₁, hT'.smul₁, smul_sub]
  add₂ a b b' f := by rw [hT.add₂, hT'.add₂]; abel
  smul₂ q a b f := by rw [hT.smul₂, hT'.smul₂, smul_sub]
  add₃ a b f f' := by rw [hT.add₃, hT'.add₃]; abel
  smul₃ q a b f := by rw [hT.smul₃, hT'.smul₃, smul_sub]
end GeneralPieces.LemQ.Tri
