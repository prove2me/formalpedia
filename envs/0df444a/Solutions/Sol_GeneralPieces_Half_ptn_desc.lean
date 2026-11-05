-- Prove2me | solution 1 for GeneralPieces.Half.ptn_desc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:18:20.858723+00:00
-- url     : https://prove2.me/submissions/cd51d87c-5fa1-4bc8-ac9b-3eb6275b0ebc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Half_List
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_GeneralPieces_Half_Order
import Theorems.Thm_GeneralPieces_Half_coe_desc
import Theorems.Thm_GeneralPieces_Half_pos_desc
import Theorems.Thm_GeneralPieces_Half_toN_ptn
import Theorems.Thm_GeneralPieces_Ring_toN_injective


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Half
open AppHalfPieces Finset ClauseBound.Part GeneralPieces.Ring Groundwork ClauseBound.Alg ClauseBound.Inst.Half
namespace GeneralPieces.Half
theorem _root_.solution (ν : Ptn) : ptn (desc ν) = ν := toN_injective (by rw [toN_ptn (pos_desc ν), coe_desc])
end GeneralPieces.Half
