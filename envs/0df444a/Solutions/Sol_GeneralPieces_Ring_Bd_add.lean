-- Prove2me | solution 1 for GeneralPieces.Ring.Bd.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:35:46.345219+00:00
-- url     : https://prove2.me/submissions/4d0b444f-61ed-44f1-a0e4-15d8e4afff98

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
namespace Bd
theorem _root_.solution {f g : V} {E : ℤ} (hf : Bd f E) (hg : Bd g E) : Bd (f + g) E := fun μ hμ => by
  by_cases h : coef μ f = 0
  · refine hg μ fun h' => hμ ?_
    unfold coef at *
    rw [coeff_add, h, h', add_zero]
  · exact hf μ h
end Bd
end GeneralPieces.Ring
