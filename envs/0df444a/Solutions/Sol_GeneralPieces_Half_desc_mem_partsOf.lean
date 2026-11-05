-- Prove2me | solution 1 for GeneralPieces.Half.desc_mem_partsOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:23:24.764998+00:00
-- url     : https://prove2.me/submissions/0db5fd8d-5110-4d1d-af2e-4c773fd99111

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Half_List
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_GeneralPieces_Half_Order
import Theorems.Thm_GeneralPieces_Half_coe_desc
import Theorems.Thm_GeneralPieces_Half_pos_desc
import Theorems.Thm_ClauseBound_Part_mem_partsOf
import Theorems.Thm_GeneralPieces_Ring_mem_ptns
import Theorems.Thm_GeneralPieces_Ring_sum_toN


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Half
open AppHalfPieces Finset ClauseBound.Part GeneralPieces.Ring Groundwork ClauseBound.Alg ClauseBound.Inst.Half
namespace GeneralPieces.Half
theorem _root_.solution {h : ℕ} {ν : Ptn} (hν : ν ∈ ptns h) : desc ν ∈ partsOf h :=
  mem_partsOf.2 ⟨by rw [← Multiset.sum_coe, coe_desc, sum_toN]; exact (mem_ptns h ν).1 hν, pos_desc ν, Multiset.pairwise_sort _ _⟩
end GeneralPieces.Half
