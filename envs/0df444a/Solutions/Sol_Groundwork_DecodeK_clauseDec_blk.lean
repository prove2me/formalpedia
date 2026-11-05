-- Prove2me | solution 1 for Groundwork.DecodeK.clauseDec_blk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:29:40.01263+00:00
-- url     : https://prove2.me/submissions/07c72df5-cbce-45c6-b0e1-f43beb26976a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatStatement
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_WidthK_Decode
import Theorems.Thm_P2M_Groundwork_DecodeK_filterMap_range_getElem__24161a506b5c
import Theorems.Thm_Groundwork_DecodeK_blk_eq
import Theorems.Thm_Groundwork_Decode_blk_eq
import Theorems.Thm_Groundwork_Decode_block_flatten
import Theorems.Thm_Groundwork_Decode_slotDec_slot
import Theorems.Thm_Groundwork_Decode_slot_lt
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_ofWord_toWord
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
open Groundwork Groundwork.DecodeK
open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode
namespace Groundwork.DecodeK
theorem _root_.solution {k n : ℕ} {C : List (Lit n)} (hC : C.length ≤ k) :
    clauseDec k (Nat.log2 (2 * n) + 1) (blk k n C) = C.map fun l => (l.1.val, l.2) := by
  have key : ∀ j ∈ List.range k, slotDec (ofWord (block (Nat.log2 (2 * n) + 1) j (blk k n C))) =
      (C.map fun l => (l.1.val, l.2))[j]? := fun j hj => by
    have hj : j < k := List.mem_range.1 hj
    rw [blk_eq, block_flatten (fun l hl => by obtain ⟨_, _, rfl⟩ := List.mem_map.1 hl; simp) j (by simpa using hj)]
    simp only [List.getElem_map, List.getElem_range, ofWord_toWord (slot_lt _), slotDec_slot, List.getElem?_map]
  rw [clauseDec, List.filterMap_congr key, filterMap_range_getElem?, List.take_of_length_le (by simpa using hC)]
end Groundwork.DecodeK
