-- Prove2me | solution 1 for GeneralPieces.Ring.nordQ_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:34:08.002209+00:00
-- url     : https://prove2.me/submissions/0f65f376-64aa-4eea-9d1a-498d958b260d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge
import Theorems.Thm_GeneralPieces_Ring_foldr_nabla_smul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (ks : List ℤ) (q : ℚ) (f : V) : nordQ ks (q • f) = q • nordQ ks f := by
  unfold nordQ
  rw [foldr_nabla_smul, foldr_nabla_smul]
end GeneralPieces.Ring
