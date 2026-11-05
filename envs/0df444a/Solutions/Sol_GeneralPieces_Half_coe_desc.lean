-- Prove2me | solution 1 for GeneralPieces.Half.coe_desc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:51:50.844221+00:00
-- url     : https://prove2.me/submissions/a78498a5-ea43-4850-9a1d-712c11b603d8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Half_List
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_GeneralPieces_Half_Order

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Half
open AppHalfPieces Finset ClauseBound.Part GeneralPieces.Ring Groundwork ClauseBound.Alg ClauseBound.Inst.Half
namespace GeneralPieces.Half
theorem _root_.solution (ν : Ptn) : ((desc ν : List ℕ) : Multiset ℕ) = toN ν := Multiset.sort_eq _ _
end GeneralPieces.Half
