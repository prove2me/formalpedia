-- Prove2me | solution 1 for Groundwork.Decode.block_flatten
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:33:15.981543+00:00
-- url     : https://prove2.me/submissions/c97e03ee-3dad-4ce5-a7f6-5ac614e30749

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Data.Nat.Size
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Prog_Decode
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
open Groundwork Groundwork.Decode
open Sat3
namespace Groundwork.Decode
theorem _root_.solution {w : ℕ} : ∀ {L : List (List Bool)} (_ : ∀ l ∈ L, l.length = w) (i : ℕ) (hi : i < L.length),
    block w i L.flatten = L[i]
  | [], _, _, hi => by simp at hi
  | l :: L, h, 0, _ => by
    have hl : l.length = w := h l (by simp)
    simp only [block, Nat.zero_mul, List.drop_zero, List.flatten_cons, List.getElem_cons_zero]
    exact List.take_left' hl
  | l :: L, h, i + 1, hi => by
    have hl : l.length = w := h l (by simp)
    have ih := solution (L := L) (fun l hl => h l (List.mem_cons_of_mem _ hl)) i (by simpa using hi)
    simp only [List.getElem_cons_succ, ← ih, block, List.flatten_cons]
    rw [show (i + 1) * w = w + i * w by rw [Nat.succ_mul, Nat.add_comm], ← List.drop_drop, List.drop_left' hl]
end Groundwork.Decode
