-- Prove2me | solution 1 for GeneralPieces.Half.desc_ptn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:18:19.806838+00:00
-- url     : https://prove2.me/submissions/7ebc914c-f68d-40a7-ba8d-5ad0679d4380

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Half_List
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_GeneralPieces_Half_Order
import Theorems.Thm_GeneralPieces_Half_toN_ptn


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Half
open AppHalfPieces Finset ClauseBound.Part GeneralPieces.Ring Groundwork ClauseBound.Alg ClauseBound.Inst.Half
namespace GeneralPieces.Half
theorem _root_.solution {L : List ℕ} (hL : ClauseBound.Boson.Pos L) (hs : L.Pairwise (· ≥ ·)) : desc (ptn L) = L := by
  have h : desc (ptn L) = (toN (ptn L)).sort (· ≥ ·) := rfl
  rw [h, toN_ptn hL]
  exact List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _) hs (Multiset.coe_eq_coe.1 (Multiset.sort_eq _ _))
end GeneralPieces.Half
