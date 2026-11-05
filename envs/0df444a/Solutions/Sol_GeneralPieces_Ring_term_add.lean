-- Prove2me | solution 1 for GeneralPieces.Ring.term_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:34:41.288133+00:00
-- url     : https://prove2.me/submissions/dc77e973-bb77-4263-a344-68878a23e818

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
theorem _root_.solution (μ : List ℕ+) (ks : List ℤ) (f g : V) : term μ ks (f + g) = term μ ks f + term μ ks g := map_add (termL μ ks) f g
end GeneralPieces.Ring
