-- Prove2me | solution 1 for GeneralPieces.Half.hOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:23:14.103842+00:00
-- url     : https://prove2.me/submissions/2fd136b5-375f-44ee-a023-c28a51c2d46d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Half_List
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_GeneralPieces_Half_Order
import Theorems.Thm_ClauseBound_Part_two_le_hOf
import Theorems.Thm_ClauseBound_Part_two_pow_le_p_hOf


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Half
open AppHalfPieces Finset ClauseBound.Part GeneralPieces.Ring Groundwork ClauseBound.Alg ClauseBound.Inst.Half
namespace GeneralPieces.Half
theorem _root_.solution (lam : ℕ) : AppHalfPieces.hOf lam = ClauseBound.Part.hOf lam := by
  have hmem : ClauseBound.Part.hOf lam ∈ {h | 2 ≤ h ∧ 2 ^ lam ≤ Partitions.p h} := ⟨two_le_hOf lam, two_pow_le_p_hOf lam⟩
  refine le_antisymm (Nat.sInf_le hmem) ?_
  have h1 : AppHalfPieces.hOf lam ∈ {h | 2 ≤ h ∧ 2 ^ lam ≤ Partitions.p h} := Nat.sInf_mem ⟨_, hmem⟩
  unfold ClauseBound.Part.hOf
  exact Nat.find_min' _ h1
end GeneralPieces.Half
