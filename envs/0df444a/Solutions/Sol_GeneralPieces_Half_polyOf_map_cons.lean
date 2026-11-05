-- Prove2me | solution 1 for GeneralPieces.Half.polyOf_map_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:41:56.155484+00:00
-- url     : https://prove2.me/submissions/e3f776c6-384e-4a07-82bf-4491e29f291d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
import Theorems.Thm_GeneralPieces_Half_tpow_ptn_cons
import Theorems.Thm_GeneralPieces_Half_polyK_cons

set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.Half
namespace GeneralPieces.Half
theorem _root_.solution (c : ℤ) (j : ℕ) (A : ClauseBound.Boson.FA) :
    polyOf (A.map fun cL => (c * cL.1, j :: cL.2)) = ((c : ℚ) • X j.toPNat') * polyOf A := by
  induction A with
  | nil => simp [polyOf, polyK]
  | cons a A ih =>
    simp only [polyOf] at ih ⊢
    rw [List.map_cons, polyK_cons, polyK_cons, mul_add, ih, tpow_ptn_cons]
    congr 1
    push_cast
    rw [smul_mul_smul_comm]
end GeneralPieces.Half
