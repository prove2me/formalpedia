-- Prove2me | solution 1 for GeneralPieces.Ring.sum_toN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:28:15.804319+00:00
-- url     : https://prove2.me/submissions/721ad611-659a-4666-95e7-32bc55aefd3f

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
theorem _root_.solution (π : Ptn) : (toN π).sum = wt π := rfl
end GeneralPieces.Ring
