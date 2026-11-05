-- Prove2me | solution 1 for GeneralPieces.LemQ.sum_Pz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:13:55.826999+00:00
-- url     : https://prove2.me/submissions/5fcb6031-ed22-4f6c-b593-b7404ccc698d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_GeneralPieces_Ring_toN_injective
import Theorems.Thm_P2M_GeneralPieces_Ring_toN_map_toPNat__be122ac80f3b


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.LemQ
theorem _root_.solution (m : ℤ) (F : Multiset ℕ → ℤ) : ∑ τ ∈ ClauseBound.Boson.Pz m, F τ = ∑ τ ∈ ptnsZ m, F (toN τ) := by
  unfold ClauseBound.Boson.Pz ptnsZ
  split_ifs
  · have e : ClauseBound.Boson.P m.toNat = (ptns m.toNat).image toN := by
      unfold ClauseBound.Boson.P ptns
      rw [image_image]
      exact image_congr fun q _ => (toN_map_toPNat' fun i hi => q.parts_pos hi).symm
    rw [e, sum_image toN_injective.injOn]
  · rfl
end GeneralPieces.LemQ
