-- Prove2me | solution 1 for Groundwork.Decode.satN_toN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:32:56.818109+00:00
-- url     : https://prove2.me/submissions/a29cc19c-132d-4e26-b8da-0ec2a4769aef

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
theorem _root_.solution {n : ℕ} (φ : CNF n) : SatN (toN φ) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun i => a i.val, fun C hC => ?_⟩
    obtain ⟨l, hl, h⟩ := ha _ (List.mem_map.2 ⟨C, hC, rfl⟩)
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    exact ⟨l', hl', h⟩
  · rintro ⟨a, ha⟩
    refine ⟨fun i => if h : i < n then a ⟨i, h⟩ else false, fun D hD => ?_⟩
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hD
    obtain ⟨l, hl, h⟩ := ha C hC
    exact ⟨_, List.mem_map.2 ⟨l, hl, rfl⟩, by simp [l.1.2, h]⟩
end Groundwork.Decode
