-- Prove2me | solution 1 for GeneralPieces.sum_ApcL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:55:43.241514+00:00
-- url     : https://prove2.me/submissions/9e48e9a1-0edb-4eac-8b0a-20d7ed55de92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
import Theorems.Thm_GeneralPieces_Half_toN_ptn
import Theorems.Thm_GeneralPieces_Half_wt_ptn
import Theorems.Thm_GeneralPieces_ApcL_eq_piece

set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open Half
variable {lam h : ℕ} {ℓ : Pieces.Bits lam → List ℕ}
namespace GeneralPieces
theorem _root_.solution (hPF : PieceFacts) (hℓ : ∀ x, ClauseBound.Boson.Pos (ℓ x) ∧ (ℓ x).sum = h) (hinj : ∀ x v, (ℓ x : Multiset ℕ) = ℓ v → x = v) (hh : 1 ≤ h)
    (x y u v : Pieces.Bits lam) :
    ∑ s ∈ Icc (-(2 * h : ℤ)) (2 * h), ClauseBound.Boson.ApcL ℓ h s x y u v = h.factorial * Pieces.cross x y u v := by
  have hw : ∀ x, wt (ptn (ℓ x)) = h := fun x => by rw [wt_ptn (hℓ x).1, (hℓ x).2]
  have hi : ∀ x v, ptn (ℓ x) = ptn (ℓ v) ↔ x = v := fun x v =>
    ⟨fun e => hinj x v (by rw [← toN_ptn (hℓ x).1, ← toN_ptn (hℓ v).1, e]), fun e => by rw [e]⟩
  have h1 := hPF.sum h _ _ _ _ hh (hw x) (hw y) (hw u) (hw v)
  have h2 : ((∑ s ∈ Icc (-(2 * h : ℤ)) (2 * h), ClauseBound.Boson.ApcL ℓ h s x y u v : ℤ) : ℚ) = ((h.factorial * Pieces.cross x y u v : ℤ) : ℚ) := by
    push_cast
    rw [Finset.sum_congr rfl fun s _ => ApcL_eq_piece hPF hℓ hh s x y u v]
    unfold piece
    rw [h1, Pieces.cross]
    simp only [hi]
    split_ifs <;> simp
  exact_mod_cast h2
end GeneralPieces
