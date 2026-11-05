-- Prove2me | solution 1 for GeneralPieces.Ring.Pz_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:26:18.848805+00:00
-- url     : https://prove2.me/submissions/580ce5b0-cc4c-41d9-8c30-7b963ba1604a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
import Theorems.Thm_ClauseBound_Boson_mem_Pz
import Theorems.Thm_GeneralPieces_Ring_mem_ptnsZ
import Theorems.Thm_GeneralPieces_Ring_sum_toN
import Theorems.Thm_GeneralPieces_Ring_zero_notMem_toN
import Theorems.Thm_P2M_GeneralPieces_Ring_toN_map_toPNat__be122ac80f3b


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (m : ℤ) : ClauseBound.Boson.Pz m = (ptnsZ m).image toN := by
  ext τ
  rw [ClauseBound.Boson.mem_Pz, mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    have hpos : ∀ i ∈ τ, 0 < i := fun i hi => Nat.pos_of_ne_zero fun h0 => h2 (h0 ▸ hi)
    refine ⟨τ.map Nat.toPNat', (mem_ptnsZ m _).2 ?_, toN_map_toPNat' hpos⟩
    rw [← sum_toN, toN_map_toPNat' hpos, h1]
  · rintro ⟨μ, hμ, rfl⟩
    exact ⟨by rw [sum_toN]; exact (mem_ptnsZ m μ).1 hμ, zero_notMem_toN μ⟩
end GeneralPieces.Ring
