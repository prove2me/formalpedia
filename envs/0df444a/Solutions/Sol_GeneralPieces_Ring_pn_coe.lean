-- Prove2me | solution 1 for GeneralPieces.Ring.pn_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:29:29.560315+00:00
-- url     : https://prove2.me/submissions/850d9927-168a-4564-b440-d4382180b2e4

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
theorem _root_.solution {k : ℤ} (hk : k ≠ 0) : ((pn k : ℕ+) : ℕ) = k.natAbs := PNat.toPNat'_coe (by omega)
end GeneralPieces.Ring
