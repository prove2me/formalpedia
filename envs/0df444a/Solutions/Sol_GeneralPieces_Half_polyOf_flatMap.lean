-- Prove2me | solution 1 for GeneralPieces.Half.polyOf_flatMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:43:29.068202+00:00
-- url     : https://prove2.me/submissions/c9da81d2-e52f-4026-bbdc-2a86881a3985

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
import Theorems.Thm_GeneralPieces_Half_polyK_append
import Theorems.Thm_GeneralPieces_Half_polyOf_map_cons

set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.Half
namespace GeneralPieces.Half
theorem _root_.solution (Y : List (ℤ × ℕ)) (A : ClauseBound.Boson.FA) :
    polyOf (Y.flatMap fun cj => A.map fun cL => (cj.1 * cL.1, cj.2 :: cL.2)) = (Y.map fun cj => (cj.1 : ℚ) • (X cj.2.toPNat' : V)).sum * polyOf A := by
  induction Y with
  | nil => simp [polyOf, polyK]
  | cons a Y ih =>
    have h := polyOf_map_cons a.1 a.2 A
    simp only [polyOf] at ih h ⊢
    rw [List.flatMap_cons, polyK_append, List.map_cons, List.sum_cons, add_mul, ih, h]
end GeneralPieces.Half
