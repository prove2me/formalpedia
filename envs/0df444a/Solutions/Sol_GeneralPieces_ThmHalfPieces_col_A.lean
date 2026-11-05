-- Prove2me | solution 1 for GeneralPieces.ThmHalfPieces.col_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:41:02.05796+00:00
-- url     : https://prove2.me/submissions/1c03609c-a217-4ada-8536-d95d6cbdaede

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Theorems.Thm_GeneralPieces_ThmHalfPieces_abs_fa_le
import Theorems.Thm_GeneralPieces_ThmHalfPieces_abs_fb_le
import Theorems.Thm_GeneralPieces_ThmHalfPieces_A_col
import Theorems.Thm_GeneralPieces_ThmHalfPieces_wt_map
import Theorems.Thm_ClauseBound_Boson_Half_factors
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex
variable {lam h : ℕ} {mu : Pieces.Bits lam → Ptn}
namespace GeneralPieces.ThmHalfPieces
theorem _root_.solution (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) :
    Pieces.FactorsThrough (Pieces.colwise ((fam h mu).A s)) ((fam h mu).ccol s) (2 ^ ClauseBound.Boson.big h) :=
  ClauseBound.Boson.Half.factors (h := h) (Pieces.colwise ((fam h mu).A s)) (fun i => 2 * h - s - i)
    (fun i τ z => fa h i (s - h + i) (mu z.1) (mu z.2) (τ.map Nat.toPNat'))
    (fun i τ z' => fb (h - s - i) (mu z'.2) (τ.map Nat.toPNat') (mu z'.1))
    (fun z z' => A_col hP hmu hh s z.1 z'.1 z.2 z'.2)
    (fun i _ τ hτ z => abs_fa_le hP hh i (IsMu.wt hmu z.1) _ (by rw [IsMu.wt hmu]; omega)
      (by have := wt_map hτ; have := abs_le.1 hs; omega))
    (fun i _ τ hτ z' => abs_fb_le hP hh (IsMu.wt hmu z'.2) _
      (by have := wt_map hτ; have := abs_le.1 hs; omega) (by rw [IsMu.wt hmu]; omega))
end GeneralPieces.ThmHalfPieces
