-- Prove2me | solution 1 for GeneralPieces.ThmHalfPieces.wt_le_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:39:20.877936+00:00
-- url     : https://prove2.me/submissions/e286a53b-0083-4578-b65a-80be5d1c39a9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt
import Theorems.Thm_GeneralPieces_Ring_mem_ptnsZ


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex
variable {lam h : ℕ} {mu : Pieces.Bits lam → Ptn}
namespace GeneralPieces.ThmHalfPieces
theorem _root_.solution {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) {i : ℕ} {σ : Ptn} (hσ : σ ∈ ptnsZ (2 * h - s - i)) : wt σ ≤ 4 * h := by
  have := (mem_ptnsZ _ σ).1 hσ
  have := abs_le.1 hs
  omega
end GeneralPieces.ThmHalfPieces
