-- Prove2me | solution 1 for GeneralPieces.Half.abs_ApcL_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:47:56.637966+00:00
-- url     : https://prove2.me/submissions/b7bfd218-dc16-44f2-9bb1-314b4f7effdf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Definitions.Def_GeneralPieces_Half_Order
import Definitions.Def_GeneralPieces_Half_Size
import Theorems.Thm_GeneralPieces_ApcL_eq_piece
import Theorems.Thm_GeneralPieces_Half_isMu
import Theorems.Thm_GeneralPieces_ThmHalfPieces_abs_piece_le
import Theorems.Thm_GeneralPieces_ThmHalfPieces_bound_lt_big
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Half
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes ClauseBound.Inst.Half
namespace GeneralPieces.Half
theorem _root_.solution (hPF : PieceFacts) {lam h : ℕ} (hp : 2 ^ lam ≤ Partitions.p h) (hℓ : ∀ x : Pieces.Bits lam, ClauseBound.Boson.Pos (ell h x) ∧ (ell h x).sum = h) (hh : 1 ≤ h)
    {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) (x y u v : Pieces.Bits lam) : |ClauseBound.Boson.ApcL (ell h) h s x y u v| < 2 ^ ClauseBound.Boson.big h := by
  have h1 := ThmHalfPieces.abs_piece_le hPF (isMu hp) hh hs x y u v
  rw [← ApcL_eq_piece hPF hℓ hh] at h1
  have h2 : |ClauseBound.Boson.ApcL (ell h) h s x y u v| ≤ ((Delta h * ((2 ^ (3 * h) * 2 ^ (12 * h ^ 2)) * (h.factorial * 2 ^ (12 * h ^ 2))) : ℕ) : ℤ) := by exact_mod_cast h1
  exact h2.trans_lt (by exact_mod_cast ThmHalfPieces.bound_lt_big h)
end GeneralPieces.Half
