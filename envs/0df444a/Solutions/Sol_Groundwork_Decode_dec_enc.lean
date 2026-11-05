-- Prove2me | solution 1 for Groundwork.Decode.dec_enc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:54:46.323197+00:00
-- url     : https://prove2.me/submissions/da935266-ebb9-4a1b-abbf-ef6450623447

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Data.Nat.Size
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Prog_Decode
import Theorems.Thm_Groundwork_Decode_width_eq
import Theorems.Thm_Groundwork_Decode_block_flatten
import Theorems.Thm_Groundwork_Decode_length_blk
import Theorems.Thm_Groundwork_Decode_clauseDec_blk
import Theorems.Thm_Groundwork_Decode_takeWhile_header
import Theorems.Thm_Groundwork_Decode_dropWhile_header
import Theorems.Thm_Groundwork_Decode_enc_eq
import Theorems.Thm_Groundwork_Decode_length_body
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
open Groundwork Groundwork.Decode
open Sat3
namespace Groundwork.Decode
theorem _root_.solution {n : ℕ} {φ : CNF n} (hφ : ∀ C ∈ φ, C.length ≤ 3) : dec (enc φ) = (n, toN φ) := by
  have hB : 0 < 3 * (Nat.log2 (2 * n) + 1) := by omega
  simp only [dec, enc_eq, takeWhile_header, dropWhile_header, List.length_replicate, List.tail_cons, width_eq,
    length_body, Nat.mul_div_cancel _ hB, List.take_range, toN]
  congr 1
  rw [min_eq_left (Nat.le_mul_of_pos_right _ hB)]
  refine List.ext_getElem (by simp) fun c h1 h2 => ?_
  have hc : c < φ.length := by simpa using h1
  simp only [List.getElem_map, List.getElem_range]
  rw [block_flatten (fun l hl => by obtain ⟨C, _, rfl⟩ := List.mem_map.1 hl; exact length_blk n C) c (by simpa using hc),
    List.getElem_map, clauseDec_blk (hφ _ (List.getElem_mem hc))]
end Groundwork.Decode
