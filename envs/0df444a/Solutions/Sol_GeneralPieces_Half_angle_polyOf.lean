-- Prove2me | solution 1 for GeneralPieces.Half.angle_polyOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:46:33.061707+00:00
-- url     : https://prove2.me/submissions/9da89671-3955-4b11-9583-60f699ee924d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
import Theorems.Thm_GeneralPieces_Half_wt_ptn
import Theorems.Thm_GeneralPieces_Half_polyK_cons
import Theorems.Thm_GeneralPieces_Half_angle_add
import Theorems.Thm_GeneralPieces_Half_angle_zero
import Theorems.Thm_GeneralPieces_Half_angle_smul_tpow

set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.Half
namespace GeneralPieces.Half
theorem _root_.solution {A : ClauseBound.Boson.FA} {h : ℕ} (hA : A.Ok h) (i : ℕ) :
    angle h i (polyOf A) = polyK (fun c => (c.1 : ℚ) * ((c.2.sum + h).choose i : ℚ)) A := by
  induction A with
  | nil => exact angle_zero h i
  | cons c A ih =>
    have hc := hA c List.mem_cons_self
    simp only [polyOf] at ih ⊢
    rw [polyK_cons, polyK_cons, angle_add, angle_smul_tpow h i _ (by rw [wt_ptn hc.1]; exact hc.2), wt_ptn hc.1,
      ih fun c' hc' => hA c' (List.mem_cons_of_mem _ hc')]
end GeneralPieces.Half
