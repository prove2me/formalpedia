-- Prove2me | solution 2 for GeneralPieces.ThmHalfPieces.Rcol_le_Delta
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:32:45.525091+00:00
-- url     : https://prove2.me/submissions/c5200cf8-96d6-4d86-b05d-9ecd90025163

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

theorem solution {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) : Rcol h s ≤ Delta h := by
  exact ClauseBound.Boson.Half.sum_pz_le (fun i => 2 * h - s - i)
    (fun i j hij => by omega) (fun i _ => by have := abs_le.1 hs; omega)
