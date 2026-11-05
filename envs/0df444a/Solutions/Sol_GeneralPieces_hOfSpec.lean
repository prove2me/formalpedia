-- Prove2me | solution 1 for GeneralPieces.hOfSpec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:31:39.790202+00:00
-- url     : https://prove2.me/submissions/881c8fc9-a62a-403c-b04b-15b96fd71f5a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_Bridge
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Lex
import Definitions.Def_GeneralPieces_Ring_Lex
import Theorems.Thm_GeneralPieces_Lex_hOf_eq
import Theorems.Thm_ClauseBound_Part_two_le_hOf
import Theorems.Thm_ClauseBound_Part_two_pow_le_p_hOf


set_option autoImplicit false
section
section
open GeneralPieces
namespace GeneralPieces
theorem _root_.solution : AppHalfPieces.HOfSpec := fun lam => by
  rw [Lex.hOf_eq]
  refine ⟨ClauseBound.Part.two_le_hOf lam, ClauseBound.Part.two_pow_le_p_hOf lam, fun h h1 h2 => ?_⟩
  unfold ClauseBound.Part.hOf
  exact Nat.find_min' _ ⟨h1, h2⟩
end GeneralPieces
