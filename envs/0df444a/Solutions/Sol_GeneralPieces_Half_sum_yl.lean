-- Prove2me | solution 1 for GeneralPieces.Half.sum_yl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:45:01.70547+00:00
-- url     : https://prove2.me/submissions/bf3b79f4-3cb3-4476-8e32-a55b39f1ce92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
import Theorems.Thm_GeneralPieces_Half_sum_Icc_eq_list

set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.Half
namespace GeneralPieces.Half
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) :
    ((ClauseBound.Boson.yl n).map fun cj => (cj.1 : ℚ) • (X cj.2.toPNat' : V)).sum = (-1 : ℚ) ^ (((n.toPNat' : ℕ+) : ℕ) - 1) • y n.toPNat' := by
  have h : ((n.toPNat' : ℕ+) : ℕ) = n := PNat.toPNat'_coe hn
  rw [y, h, sum_Icc_eq_list, ClauseBound.Boson.yl, List.map_map, List.smul_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp]
  push_cast
  rw [mul_smul]
end GeneralPieces.Half
