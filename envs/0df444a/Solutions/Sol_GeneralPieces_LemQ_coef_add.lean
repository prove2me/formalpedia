-- Prove2me | solution 1 for GeneralPieces.LemQ.coef_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:10:01.566654+00:00
-- url     : https://prove2.me/submissions/c7a450a8-dcb6-4b56-9e35-65432be3ed26

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
theorem _root_.solution (π : Ptn) (f g : V) : coef π (f + g) = coef π f + coef π g := coeff_add _ _ _
end GeneralPieces.LemQ
