-- Prove2me | solution 1 for GeneralPieces.Bits.exists_bits_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:40:34.888672+00:00
-- url     : https://prove2.me/submissions/a1ecd501-3c62-4e61-8a19-43aaeef6a8ab

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Sizes
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_Bits
import Theorems.Thm_GeneralPieces_Bits_bits_le
import Theorems.Thm_GeneralPieces_Bits_exists_display_le
import Theorems.Thm_GeneralPieces_Bits_four_mul_rho

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Bits
open AppHalfPieces Finset Partitions Real GeneralPieces.Lex GeneralPieces.Sizes
variable {B C : ℝ}
namespace GeneralPieces.Bits
theorem _root_.solution (hB : Bounds B C) : ∃ c : ℕ, ∀ lam : ℕ, 1 ≤ lam → ∀ s : ℤ, |s| ≤ 2 * (AppHalfPieces.hOf lam : ℤ) →
    ((Nat.clog 2 (Rrow (AppHalfPieces.hOf lam) s) + Nat.clog 2 (Rcol (AppHalfPieces.hOf lam) s) : ℕ) : ℝ) ≤ 4 * (1 / √2) * lam + c * logb 2 (2 * lam) := by
  obtain ⟨c, hc⟩ := exists_display_le hB
  exact ⟨c, fun lam hl s hs => by rw [four_mul_rho]; exact (bits_le hB hs).trans (hc lam hl)⟩
end GeneralPieces.Bits
