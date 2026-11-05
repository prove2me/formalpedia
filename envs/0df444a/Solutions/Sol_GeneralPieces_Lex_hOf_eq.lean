-- Prove2me | solution 1 for GeneralPieces.Lex.hOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:30:26.472864+00:00
-- url     : https://prove2.me/submissions/c611b85c-946c-4973-b49b-ab7c6e228dba

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_Bridge
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Lex
import Definitions.Def_GeneralPieces_Ring_Lex
import Theorems.Thm_ClauseBound_Part_two_le_hOf
import Theorems.Thm_ClauseBound_Part_two_pow_le_p_hOf


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Lex
open AppHalfPieces Finset
namespace GeneralPieces.Lex
theorem _root_.solution (lam : ℕ) : AppHalfPieces.hOf lam = ClauseBound.Part.hOf lam := by
  have hne : {h | 2 ≤ h ∧ 2 ^ lam ≤ Partitions.p h}.Nonempty := ClauseBound.Part.exists_h lam
  refine le_antisymm (Nat.sInf_le ⟨ClauseBound.Part.two_le_hOf lam, ClauseBound.Part.two_pow_le_p_hOf lam⟩) ?_
  unfold ClauseBound.Part.hOf
  exact Nat.find_min' _ (Nat.sInf_mem hne)
end GeneralPieces.Lex
