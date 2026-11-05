-- Prove2me | solution 1 for GeneralPieces.Ring.isInt_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:41:19.874904+00:00
-- url     : https://prove2.me/submissions/fa8acfa9-8ff9-4813-b94b-04c7d1269461

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
import Theorems.Thm_GeneralPieces_Ring_isInt_zero
import Theorems.Thm_GeneralPieces_Ring_isInt_add

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {ι : Type} (s : Finset ι) (F : ι → V) (h : ∀ i ∈ s, IsInt (F i)) : IsInt (∑ i ∈ s, F i) :=
  sum_induction F IsInt (fun _ _ => isInt_add) isInt_zero h
end GeneralPieces.Ring
