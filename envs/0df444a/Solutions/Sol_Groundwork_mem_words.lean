-- Prove2me | solution 1 for Groundwork.mem_words
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:31:43.734242+00:00
-- url     : https://prove2.me/submissions/c4044c33-2cc4-41fc-9331-512988f0318d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.TakeDrop
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_StepMachines_Prog_Chunks
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_ofWord_lt
import Theorems.Thm_Groundwork_toWord_ofWord
attribute [local simp] Groundwork.length_toWord

set_option autoImplicit false
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution {ℓ : ℕ} {w : List Bool} : w ∈ words ℓ ↔ w.length = ℓ := by
  simp only [words, mem_image, mem_range]
  constructor
  · rintro ⟨y, _, rfl⟩; simp
  · rintro rfl; exact ⟨ofWord w, ofWord_lt w, toWord_ofWord w⟩
end Groundwork
