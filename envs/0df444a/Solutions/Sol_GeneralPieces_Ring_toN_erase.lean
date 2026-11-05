-- Prove2me | solution 1 for GeneralPieces.Ring.toN_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:30:48.694051+00:00
-- url     : https://prove2.me/submissions/b1e35cb7-8796-4914-b747-41c86d95190a

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
theorem _root_.solution (π : Ptn) (l : ℕ+) : toN (π.erase l) = (toN π).erase (l : ℕ) := Multiset.map_erase _ PNat.coe_injective l π
end GeneralPieces.Ring
