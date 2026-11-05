-- Prove2me | solution 1 for GeneralPieces.Consts.numbers_of_thmHalfPieces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:51.60084+00:00
-- url     : https://prove2.me/submissions/226283f1-7526-4531-a102-c1fb851e5f8f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_GeneralPieces_Half_Consts

set_option autoImplicit false
section
section
open GeneralPieces
open Finset Real ClauseBound.Inst.Half
open GeneralPieces.Consts
namespace GeneralPieces.Consts
theorem _root_.solution (hT : AppHalfPieces.ThmHalfPiecesPure) : ∃ c : ℕ, ∀ lam : ℕ, 1 ≤ lam →
    4 * AppHalfPieces.hOf lam + 1 ≤ (2 * lam) ^ c ∧ (AppHalfPieces.hOf lam).factorial < 2 ^ (2 * lam) ^ c ∧
    ∀ s : ℤ, |s| ≤ 2 * (AppHalfPieces.hOf lam : ℤ) →
      ((Nat.clog 2 (AppHalfPieces.Rrow (AppHalfPieces.hOf lam) s) + Nat.clog 2 (AppHalfPieces.Rcol (AppHalfPieces.hOf lam) s) : ℕ) : ℝ) ≤ 4 * (1 / √2) * lam + c * logb 2 (2 * lam) := by
  obtain ⟨c, H⟩ := hT
  refine ⟨c, fun lam hl => ?_⟩
  obtain ⟨mu, P, -, hP, hd, hI, -, hrow, hcol⟩ := H lam hl
  refine ⟨?_, ?_, fun s hs => ?_⟩
  · have h1 := hP.card_I
    rw [hI, Int.card_Icc] at h1
    omega
  · have h1 := hP.abs_d
    rw [hd] at h1
    exact_mod_cast h1
  · have h1 := hP.caps s (by rw [hI]; exact mem_Icc.2 (abs_le.1 hs))
    rwa [hrow, hcol] at h1
end GeneralPieces.Consts
