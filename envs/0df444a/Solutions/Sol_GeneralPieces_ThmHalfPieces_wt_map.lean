-- Prove2me | solution 1 for GeneralPieces.ThmHalfPieces.wt_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:28:46.524199+00:00
-- url     : https://prove2.me/submissions/45513206-9f4d-4ac8-9123-1718b8ffd5fb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt
import Theorems.Thm_GeneralPieces_Ring_Pz_eq
import Theorems.Thm_GeneralPieces_Ring_mem_ptnsZ
import Theorems.Thm_P2M_GeneralPieces_Ring_map_toPNat__toN_169eea647133


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex
variable {lam h : ℕ} {mu : Pieces.Bits lam → Ptn}
namespace GeneralPieces.ThmHalfPieces
theorem _root_.solution {m : ℤ} {τ : Multiset ℕ} (hτ : τ ∈ ClauseBound.Boson.Pz m) : (wt (τ.map Nat.toPNat') : ℤ) = m := by
  rw [Pz_eq] at hτ
  obtain ⟨σ, hσ, rfl⟩ := mem_image.1 hτ
  rw [map_toPNat'_toN]
  exact (mem_ptnsZ m σ).1 hσ
end GeneralPieces.ThmHalfPieces
