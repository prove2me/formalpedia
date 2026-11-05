-- Prove2me | solution 1 for Groundwork.Sparsify.exists_of_mem_leaves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:31:36.246732+00:00
-- url     : https://prove2.me/submissions/609e90d3-61d7-4718-9221-18aaf8994ec5

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
theorem _root_.solution
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (k : ℕ) (s : σ) (p t : ℕ) (hG : G s p t) : ∀ x ∈ leaves step k s, ∃ p' t', G x p' t' := by
  induction k generalizing s p t with
  | zero =>
    intro x hx
    obtain rfl : x = s := by simpa [leaves] using hx
    exact ⟨p, t, hG⟩
  | succ k ih =>
    intro x hx
    rw [leaves] at hx
    split at hx
    · obtain rfl : x = s := by simpa using hx
      exact ⟨p, t, hG⟩
    · rename_i l r h0
      obtain ⟨hl, hr⟩ := hs s p t l r hG h0
      rcases List.mem_append.1 hx with hx | hx
      · exact ih l (p + 1) t hl x hx
      · exact ih r (p + 1) (t + q) hr x hx
end Groundwork.Sparsify
