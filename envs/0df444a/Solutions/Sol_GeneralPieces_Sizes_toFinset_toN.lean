-- Prove2me | solution 1 for GeneralPieces.Sizes.toFinset_toN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:27:48.247167+00:00
-- url     : https://prove2.me/submissions/e4703c4d-bc36-4630-b90a-de837d351d1a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution (π : Ptn) : (toN π).toFinset = π.toFinset.image fun k : ℕ+ => (k : ℕ) := Multiset.toFinset_map _ _
end GeneralPieces.Sizes
