-- Prove2me | solution 1 for GeneralPieces.Ring.Bd.smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:35:59.724907+00:00
-- url     : https://prove2.me/submissions/a5b9f2ab-f908-4c9b-9488-a6dc657d7d86

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_ClauseBound_Boson_Text_coef_smul
import Theorems.Thm_GeneralPieces_Ring_coef_smul


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
namespace Bd
theorem _root_.solution {f : V} {E : ℤ} (hf : Bd f E) (q : ℚ) : Bd (q • f) E := fun μ hμ => hf μ fun h => hμ (by rw [coef_smul, h, mul_zero])
end Bd
end GeneralPieces.Ring
