-- Prove2me | solution 1 for GeneralPieces.Ring.coef_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:41:30.260477+00:00
-- url     : https://prove2.me/submissions/5a20cf18-6a3c-4b9b-b56c-307525e1d48c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {ι : Type} (π : Ptn) (s : Finset ι) (F : ι → V) : coef π (∑ i ∈ s, F i) = ∑ i ∈ s, coef π (F i) := by
  unfold coef
  rw [coeff_sum]
end GeneralPieces.Ring
