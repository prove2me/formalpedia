-- Prove2me | solution 1 for Groundwork.Decode.clauseDec_blk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:45:34.796585+00:00
-- url     : https://prove2.me/submissions/dfc1f980-975b-443e-b681-1037a6b6fce1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Data.Nat.Size
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Prog_Decode
import Theorems.Thm_Groundwork_Decode_slot_lt
import Theorems.Thm_Groundwork_Decode_slotDec_slot
import Theorems.Thm_Groundwork_Decode_block_flatten
import Theorems.Thm_Groundwork_Decode_blk_eq
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_ofWord_toWord
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
open Groundwork Groundwork.Decode
open Sat3
namespace Groundwork.Decode
theorem _root_.solution {n : ℕ} {C : List (Lit n)} (hC : C.length ≤ 3) :
    clauseDec ((Nat.log2 (2 * n) + 1)) (blk n C) = C.map fun l => (l.1.val, l.2) := by
  have hw : ∀ l ∈ [toWord ((Nat.log2 (2 * n) + 1)) (slot C[0]?), toWord ((Nat.log2 (2 * n) + 1)) (slot C[1]?),
      toWord ((Nat.log2 (2 * n) + 1)) (slot C[2]?)], l.length = (Nat.log2 (2 * n) + 1) := by simp
  have h0 := block_flatten hw 0 (by simp)
  have h1 := block_flatten hw 1 (by simp)
  have h2 := block_flatten hw 2 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2
  simp only [clauseDec, blk_eq, List.filterMap_cons, List.filterMap_nil, h0, h1, h2, ofWord_toWord (slot_lt _),
    slotDec_slot]
  match C, hC with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _, h => simp at h; omega
end Groundwork.Decode
