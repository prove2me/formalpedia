-- Prove2me | solution 1 for GeneralPieces.ApcL_eq_piece
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:49:07.772196+00:00
-- url     : https://prove2.me/submissions/a5bf1962-290d-42bf-81ee-a55603bdea1f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
import Theorems.Thm_GeneralPieces_Half_toN_ptn
import Theorems.Thm_GeneralPieces_Half_wt_ptn
import Theorems.Thm_GeneralPieces_Half_botK_eq
import Theorems.Thm_GeneralPieces_Half_topK_eq
import Theorems.Thm_ClauseBound_Boson_ApcL_col_eq
import Theorems.Thm_GeneralPieces_Ring_sum_Pz


set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open Half
variable {lam h : ℕ} {ℓ : Pieces.Bits lam → List ℕ}
namespace GeneralPieces
theorem _root_.solution (hPF : PieceFacts) (hℓ : ∀ x, ClauseBound.Boson.Pos (ℓ x) ∧ (ℓ x).sum = h) (hh : 1 ≤ h) (s : ℤ) (x y u v : Pieces.Bits lam) :
    ((ClauseBound.Boson.ApcL ℓ h s x y u v : ℤ) : ℚ) = piece h (fun x => ptn (ℓ x)) s x y u v := by
  have hw : ∀ x, wt (ptn (ℓ x)) = h := fun x => by rw [wt_ptn (hℓ x).1, (hℓ x).2]
  rw [piece, hPF.col h _ _ _ _ s hh (hw x) (hw y) (hw u) (hw v), ClauseBound.Boson.ApcL_col_eq hℓ]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_Pz]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← toN_ptn (hℓ u).1, ← toN_ptn (hℓ y).1, topK_eq (hℓ x).1 (hℓ x).2, botK_eq (hℓ v).1 (hℓ v).2]
end GeneralPieces
