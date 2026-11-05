-- Prove2me | solution 1 for GeneralPieces.Half.pos_desc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:15:26.297275+00:00
-- url     : https://prove2.me/submissions/6b3dae1c-f828-4adb-b9f2-e06f7d0fd25e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Half_List
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_GeneralPieces_Half_Order
import Theorems.Thm_GeneralPieces_Half_coe_desc
import Theorems.Thm_GeneralPieces_Ring_zero_notMem_toN


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Half
open AppHalfPieces Finset ClauseBound.Part GeneralPieces.Ring Groundwork ClauseBound.Alg ClauseBound.Inst.Half
namespace GeneralPieces.Half
theorem _root_.solution (ν : Ptn) : ClauseBound.Boson.Pos (desc ν) := fun n hn => by
  have h1 : n ∈ toN ν := by rw [← coe_desc]; exact Multiset.mem_coe.2 hn
  exact Nat.pos_of_ne_zero fun h0 => zero_notMem_toN ν (h0 ▸ h1)
end GeneralPieces.Half
