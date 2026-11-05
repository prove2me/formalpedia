-- Prove2me | solution 1 for GeneralPieces.ApcL_row_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:55:47.365204+00:00
-- url     : https://prove2.me/submissions/2ef3b5a4-b610-4f8f-8752-1374fdb7dcf8

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
import Theorems.Thm_GeneralPieces_ApcL_eq_piece
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
    ClauseBound.Boson.ApcL ℓ h s x y u v = ∑ i ∈ range (2 * h + 1), ∑ τ ∈ ClauseBound.Boson.Pz (s + i),
      ClauseBound.Boson.topK (ℓ x) h i (s - h + i) τ (ℓ y : Multiset ℕ) * ClauseBound.Boson.botK (ℓ v) h (h - s - i) (ℓ u : Multiset ℕ) τ := by
  have hw : ∀ x, wt (ptn (ℓ x)) = h := fun x => by rw [wt_ptn (hℓ x).1, (hℓ x).2]
  have h2 : ((ClauseBound.Boson.ApcL ℓ h s x y u v : ℤ) : ℚ) = ((∑ i ∈ range (2 * h + 1), ∑ τ ∈ ClauseBound.Boson.Pz (s + i),
      ClauseBound.Boson.topK (ℓ x) h i (s - h + i) τ (ℓ y : Multiset ℕ) * ClauseBound.Boson.botK (ℓ v) h (h - s - i) (ℓ u : Multiset ℕ) τ : ℤ) : ℚ) := by
    rw [ApcL_eq_piece hPF hℓ hh, piece, hPF.row h _ _ _ _ s hh (hw x) (hw y) (hw u) (hw v)]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_Pz]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← toN_ptn (hℓ u).1, ← toN_ptn (hℓ y).1, topK_eq (hℓ x).1 (hℓ x).2, botK_eq (hℓ v).1 (hℓ v).2]
  exact_mod_cast h2
end GeneralPieces
