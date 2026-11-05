-- Prove2me | solution 1 for GeneralPieces.ThmHalfPieces.A_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:39:12.394002+00:00
-- url     : https://prove2.me/submissions/38fc9b17-da9c-49ec-b68c-d23c964ec2f4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Theorems.Thm_GeneralPieces_ThmHalfPieces_piece_col
import Theorems.Thm_GeneralPieces_Ring_sum_Pz
import Theorems.Thm_P2M_GeneralPieces_Ring_map_toPNat__toN_169eea647133


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex
variable {lam h : ℕ} {mu : Pieces.Bits lam → Ptn}
namespace GeneralPieces.ThmHalfPieces
theorem _root_.solution (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) (s : ℤ) (x y u v : Pieces.Bits lam) :
    (fam h mu).A s x y u v = ∑ i ∈ range (2 * h + 1), ∑ τ ∈ ClauseBound.Boson.Pz (2 * h - s - i),
      fa h i (s - h + i) (mu x) (mu u) (τ.map Nat.toPNat') * fb (h - s - i) (mu v) (τ.map Nat.toPNat') (mu y) := by
  change (piece h mu s x y u v).num = _
  rw [piece_col hP hmu hh, Rat.num_intCast]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_Pz]
  exact sum_congr rfl fun σ _ => by rw [map_toPNat'_toN]
end GeneralPieces.ThmHalfPieces
