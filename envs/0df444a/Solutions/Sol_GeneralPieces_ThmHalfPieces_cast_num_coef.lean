-- Prove2me | solution 1 for GeneralPieces.ThmHalfPieces.cast_num_coef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:26:04.683258+00:00
-- url     : https://prove2.me/submissions/21804147-54a5-471a-94bc-c0c34bd7f82e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex
namespace GeneralPieces.ThmHalfPieces
theorem _root_.solution {f : V} (hf : IsInt f) (μ : Ptn) : (((coef μ f).num : ℤ) : ℚ) = coef μ f := by
  obtain ⟨z, hz⟩ := hf (Multiset.toFinsupp μ)
  unfold coef
  rw [hz, Rat.num_intCast]
end GeneralPieces.ThmHalfPieces
