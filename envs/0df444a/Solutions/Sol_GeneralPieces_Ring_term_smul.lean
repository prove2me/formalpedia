-- Prove2me | solution 1 for GeneralPieces.Ring.term_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:35:02.915812+00:00
-- url     : https://prove2.me/submissions/76902de3-8f3e-44c9-889d-d7ed23c2a837

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
theorem _root_.solution (μ : List ℕ+) (ks : List ℤ) (q : ℚ) (f : V) : term μ ks (q • f) = q • term μ ks f := map_smul (termL μ ks) q f
end GeneralPieces.Ring
