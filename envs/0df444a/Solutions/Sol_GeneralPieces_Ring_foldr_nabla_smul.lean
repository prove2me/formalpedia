-- Prove2me | solution 1 for GeneralPieces.Ring.foldr_nabla_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:30:04.300019+00:00
-- url     : https://prove2.me/submissions/00c74f3e-fed1-44cb-b1a2-6e95ab9515c0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge
import Theorems.Thm_GeneralPieces_Ring_nabla_smul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (l : List ℤ) (q : ℚ) (f : V) : l.foldr nabla (q • f) = q • l.foldr nabla f := by
  induction l with
  | nil => rfl
  | cons k l ih => rw [List.foldr_cons, List.foldr_cons, ih, nabla_smul]
end GeneralPieces.Ring
