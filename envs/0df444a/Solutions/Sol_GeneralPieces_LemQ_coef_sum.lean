-- Prove2me | solution 1 for GeneralPieces.LemQ.coef_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:29:16.772433+00:00
-- url     : https://prove2.me/submissions/f58a8531-5eaa-4755-a0f6-853363ff9440

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
theorem _root_.solution {ι : Type} (π : Ptn) (s : Finset ι) (F : ι → V) : coef π (∑ i ∈ s, F i) = ∑ i ∈ s, coef π (F i) := coeff_sum _ _ _
end GeneralPieces.LemQ
