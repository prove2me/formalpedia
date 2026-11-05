-- Prove2me | solution 1 for Groundwork.Sparsify.stack_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:41:30.279198+00:00
-- url     : https://prove2.me/submissions/f9ff5b98-6bf2-4288-a9b1-130bff996904

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Function.Iterate
import Definitions.Def_StepMachines_Math_SparsifyTree
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {σ : Type*} (step : σ → Option (σ × σ))
variable {step} {G : σ → ℕ → ℕ → Prop} {D T q : ℕ}
namespace Groundwork.Sparsify
theorem _root_.solution (hb : ∀ s p t, G s p t → p ≤ D ∧ t ≤ T)
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (s : σ) (p t : ℕ) (hG : G s p t) (i : ℕ) :
    ((round step)^[i] ([s], [])).1.length ≤ D + 1 ∧ ∀ x ∈ ((round step)^[i] ([s], [])).1, ∃ p' t', G x p' t' := by
  have hok : StackOK G ((round step)^[i] ([s], [])).1 := by
    induction i with
    | zero => exact ⟨⟨p, t, hG, Nat.zero_le _⟩, trivial⟩
    | succ i ih => rw [Function.iterate_succ_apply']; exact ih.round hs
  refine ⟨?_, hok.mem⟩
  generalize ((round step)^[i] ([s], [])).1 = st at hok
  obtain _ | ⟨x, r⟩ := st
  · simp
  · obtain ⟨⟨p', t', hG', hp'⟩, -⟩ := hok
    have := (hb _ _ _ hG').1
    simp only [List.length_cons]
    omega
end Groundwork.Sparsify
