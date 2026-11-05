-- Prove2me | solution 3 for GeneralPieces.ThmHalfPieces.Rcol_le_Delta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:40:41.855017+00:00
-- url     : https://prove2.me/submissions/e9215f6b-168e-4d81-80cd-54f36f2ee93a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Theorems.Thm_ClauseBound_Boson_Half_sum_pz_le


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex
variable {lam h : ℕ} {mu : Pieces.Bits lam → Ptn}
namespace GeneralPieces.ThmHalfPieces
theorem _root_.solution {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) : Rcol h s ≤ Delta h :=
  ClauseBound.Boson.Half.sum_pz_le (fun i => 2 * h - s - i) (fun i j hij => by omega) (fun i _ => by have := abs_le.1 hs; omega)
end GeneralPieces.ThmHalfPieces
