-- Prove2me | solution 2 for GeneralPieces.Pcs.tpow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:24:14.562786+00:00
-- url     : https://prove2.me/submissions/cf142b3a-6d1b-4278-bcbe-3f128bda0be3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
theorem _root_.solution (μ ν : Ptn) : tpow μ * tpow ν = tpow (μ + ν) := by
  unfold tpow
  rw [monomial_mul, map_add, one_mul]
end GeneralPieces.Pcs
