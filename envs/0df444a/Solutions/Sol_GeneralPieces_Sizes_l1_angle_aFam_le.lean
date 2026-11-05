-- Prove2me | solution 1 for GeneralPieces.Sizes.l1_angle_aFam_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:34:34.363785+00:00
-- url     : https://prove2.me/submissions/a1f257f5-5690-48df-9949-95118bfef430

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Sizes_l1_aFam_le
import Theorems.Thm_GeneralPieces_Sizes_l1_angle_le
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution {h : ℕ} (i : ℕ) {μ : Ptn} (hμ : wt μ = h) : l1 (angle h i (aFam μ)) ≤ 2 ^ (3 * h) := by
  calc _ ≤ 2 ^ (2 * h) * l1 (aFam μ) := l1_angle_le h i _
    _ ≤ 2 ^ (2 * h) * 2 ^ h := mul_le_mul_of_nonneg_left (hμ ▸ l1_aFam_le μ) (by positivity)
    _ = 2 ^ (3 * h) := by rw [← pow_add]; congr 1; ring
end GeneralPieces.Sizes
