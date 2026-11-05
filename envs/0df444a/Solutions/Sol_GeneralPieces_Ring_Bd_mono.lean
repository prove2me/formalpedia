-- Prove2me | solution 1 for GeneralPieces.Ring.Bd.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:27:02.418251+00:00
-- url     : https://prove2.me/submissions/d91eb6e9-8476-4a0c-b7e3-bb63bc4697c6

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
theorem _root_.solution {f : V} {E E' : ℤ} (h : Bd f E) (hE : E ≤ E') : Bd f E' := fun μ hμ => (h μ hμ).trans hE
end Bd
end GeneralPieces.Ring
