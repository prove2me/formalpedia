-- Prove2me | solution 1 for GeneralPieces.LemQ.Tri.smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:29:20.395362+00:00
-- url     : https://prove2.me/submissions/fc359dfd-e25e-4099-8bdd-af029d9eb6da

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
theorem _root_.solution (hT : Tri T) (c : ℚ) : Tri fun a b f => c • T a b f where
  add₁ a a' b f := by rw [hT.add₁, smul_add]
  smul₁ q a b f := by rw [hT.smul₁, smul_comm]
  add₂ a b b' f := by rw [hT.add₂, smul_add]
  smul₂ q a b f := by rw [hT.smul₂, smul_comm]
  add₃ a b f f' := by rw [hT.add₃, smul_add]
  smul₃ q a b f := by rw [hT.smul₃, smul_comm]
end GeneralPieces.LemQ.Tri
