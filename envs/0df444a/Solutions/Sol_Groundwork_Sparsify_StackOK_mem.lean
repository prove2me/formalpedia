-- Prove2me | solution 1 for Groundwork.Sparsify.StackOK.mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:20:52.075976+00:00
-- url     : https://prove2.me/submissions/7ba9f28a-5223-496f-8e80-7ccb1a485228

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Function.Iterate
import Definitions.Def_StepMachines_Math_SparsifyTree

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {σ : Type*} (step : σ → Option (σ × σ))
variable {step} {G : σ → ℕ → ℕ → Prop} {D T q : ℕ}
namespace Groundwork.Sparsify
namespace StackOK
theorem _root_.solution {st : List σ} (h : StackOK G st) : ∀ x ∈ st, ∃ p t, G x p t := by
  induction st with
  | nil => simp
  | cons s r ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · obtain ⟨⟨p, t, hG, -⟩, -⟩ := h
      exact ⟨p, t, hG⟩
    · exact ih h.2 x hx
end StackOK
end Groundwork.Sparsify
