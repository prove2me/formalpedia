-- Prove2me | solution 1 for GeneralPieces.Ring.nabla_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:17:37.572448+00:00
-- url     : https://prove2.me/submissions/ec4c2d03-0d36-4b3c-92bf-88fa1b366f85

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
theorem _root_.solution {ι : Type} (k : ℤ) (s : Finset ι) (F : ι → V) : nabla k (∑ i ∈ s, F i) = ∑ i ∈ s, nabla k (F i) := map_sum (nablaL k) F s
end GeneralPieces.Ring
