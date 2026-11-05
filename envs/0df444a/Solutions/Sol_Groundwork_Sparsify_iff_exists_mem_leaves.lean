-- Prove2me | solution 1 for Groundwork.Sparsify.iff_exists_mem_leaves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:22:41.897806+00:00
-- url     : https://prove2.me/submissions/61ca2c99-4aed-4e73-9b6c-d7cf02ffd190

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
    (S : σ → Prop) (hS : ∀ s p t l h, G s p t → step s = some (l, h) → (S s ↔ S l ∨ S h))
    (k : ℕ) (s : σ) (p t : ℕ) (hG : G s p t) : S s ↔ ∃ x ∈ leaves step k s, S x := by
  induction k generalizing s p t with
  | zero => simp [leaves]
  | succ k ih =>
    rw [leaves]
    split
    · simp
    · rename_i l r h0
      obtain ⟨hl, hr⟩ := hs s p t l r hG h0
      rw [hS s p t l r hG h0, ih l (p + 1) t hl, ih r (p + 1) (t + q) hr]
      simp only [List.mem_append, or_and_right, exists_or]
end Groundwork.Sparsify
