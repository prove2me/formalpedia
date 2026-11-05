-- Prove2me | solution 1 for GeneralPieces.Half.angle_smul_tpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:44:58.702206+00:00
-- url     : https://prove2.me/submissions/a7c16fe6-c6c0-4459-bcbb-a90c171af55d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
import Theorems.Thm_GeneralPieces_Half_part_tpow

set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.Half
namespace GeneralPieces.Half
theorem _root_.solution (h i : ℕ) (q : ℚ) {μ : Ptn} (hμ : wt μ ≤ h) : angle h i (q • tpow μ) = (q * ((wt μ + h).choose i : ℚ)) • tpow μ := by
  unfold angle
  rw [Finset.sum_eq_single_of_mem (wt μ) (Finset.mem_range.2 (by omega))]
  · rw [part, map_smul, ← part, part_tpow, if_pos rfl, smul_smul, mul_comm]
  · intro h' _ hne
    rw [part, map_smul, ← part, part_tpow, if_neg hne, smul_zero, smul_zero]
end GeneralPieces.Half
