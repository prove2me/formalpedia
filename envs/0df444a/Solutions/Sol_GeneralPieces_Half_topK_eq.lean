-- Prove2me | solution 1 for GeneralPieces.Half.topK_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:47:55.872535+00:00
-- url     : https://prove2.me/submissions/8b1be561-a476-456e-b54d-0272ade8735d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
import Theorems.Thm_GeneralPieces_Half_aFam_eq
import Theorems.Thm_GeneralPieces_Half_angle_polyOf
import Theorems.Thm_GeneralPieces_Half_coef_op_polyK
import Theorems.Thm_ClauseBound_Boson_aFam_ok


set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.Half
namespace GeneralPieces.Half
theorem _root_.solution {L : List ℕ} {h : ℕ} (hL : ClauseBound.Boson.Pos L) (hs : L.sum = h) (i : ℕ) (r : ℤ) (π σ : Ptn) :
    ((ClauseBound.Boson.topK L h i r (toN π) (toN σ) : ℤ) : ℚ) = (-1) ^ i * coef π (op (angle h i (AppHalfPieces.aFam (ptn L))) r (tpow σ)) := by
  have hA : (ClauseBound.Boson.aFam L).Ok h := by
    have := ClauseBound.Boson.aFam_ok hL
    rwa [hs] at this
  rw [aFam_eq hL, angle_polyOf hA, coef_op_polyK _ (fun c hc => (hA c hc).1), ClauseBound.Boson.topK]
  push_cast
  congr 1
  induction ClauseBound.Boson.aFam L with
  | nil => simp
  | cons c A ih => simp only [List.map_cons, List.sum_cons]; push_cast; rw [ih]
end GeneralPieces.Half
