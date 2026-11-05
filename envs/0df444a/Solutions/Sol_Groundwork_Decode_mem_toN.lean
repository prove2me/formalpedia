-- Prove2me | solution 1 for Groundwork.Decode.mem_toN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:32:42.640779+00:00
-- url     : https://prove2.me/submissions/8cc9108b-7bb6-4177-a17b-a52c0b20245c

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
theorem _root_.solution {n : ℕ} {φ : CNF n} {D : List (ℕ × Bool)} (hD : D ∈ toN φ) :
    (∃ C ∈ φ, D.length = C.length) ∧ ∀ l ∈ D, l.1 < n := by
  obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hD
  refine ⟨⟨C, hC, by simp⟩, fun l hl => ?_⟩
  obtain ⟨l', _, rfl⟩ := List.mem_map.1 hl
  exact l'.1.2
end Groundwork.Decode
