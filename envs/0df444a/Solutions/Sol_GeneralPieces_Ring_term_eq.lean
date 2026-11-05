-- Prove2me | solution 1 for GeneralPieces.Ring.term_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:28:14.822063+00:00
-- url     : https://prove2.me/submissions/2d560568-d5d6-4925-9120-dccc025c9f3e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (μ : List ℕ+) (ks : List ℤ) (f : V) : term μ ks f = ((wtQ μ ks : ℤ) : ℚ) • nordQ ks f := rfl
end GeneralPieces.Ring
