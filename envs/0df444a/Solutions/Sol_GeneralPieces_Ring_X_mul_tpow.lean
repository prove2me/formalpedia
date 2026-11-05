-- Prove2me | solution 1 for GeneralPieces.Ring.X_mul_tpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:40:30.994832+00:00
-- url     : https://prove2.me/submissions/4d044ab0-3cd5-4f66-97f0-97f7abf035e0

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
theorem _root_.solution (n : ℕ+) (μ : Ptn) : X n * tpow μ = tpow (n ::ₘ μ) := by
  unfold tpow X
  rw [monomial_mul, one_mul, ← Multiset.singleton_add, map_add, Multiset.toFinsupp_singleton]
end GeneralPieces.Ring
