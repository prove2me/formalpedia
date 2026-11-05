-- Prove2me | solution 1 for Groundwork.Sparsify.leaves_sim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:11:15.795146+00:00
-- url     : https://prove2.me/submissions/a6d99880-5526-48cd-b198-6ea283b4b598

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SparsifyStep
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_ThreeSatStatement
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_StepMachines_Math_SparsifyList

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {σ σ' : Type*} {step' : σ' → Option (σ' × σ')} {step : σ → Option (σ × σ)} {f : σ' → σ} {I : σ' → Prop}
namespace Groundwork.Sparsify
theorem _root_.solution (hsim : ∀ s, I s → (step' s).map (Prod.map f f) = step (f s))
    (hinv : ∀ s l h, I s → step' s = some (l, h) → I l ∧ I h) (k : ℕ) (s : σ') (hs : I s) :
    (leaves step' k s).map f = leaves step k (f s) ∧ ∀ x ∈ leaves step' k s, I x := by
  induction k generalizing s with
  | zero => simp [leaves, hs]
  | succ k ih =>
    have h1 := hsim s hs
    cases h0 : step' s with
    | none =>
      rw [h0] at h1
      simp [leaves, h0, ← h1, hs]
    | some lh =>
      obtain ⟨l, h⟩ := lh
      rw [h0] at h1
      obtain ⟨hl, hh⟩ := hinv s l h hs h0
      have e : leaves step (k + 1) (f s) = leaves step k (f l) ++ leaves step k (f h) := by
        simp [leaves, ← h1]
      have e' : leaves step' (k + 1) s = leaves step' k l ++ leaves step' k h := by simp [leaves, h0]
      rw [e, e', List.map_append, (ih l hl).1, (ih h hh).1]
      refine ⟨rfl, fun x hx => ?_⟩
      rcases List.mem_append.1 hx with hx | hx
      exacts [(ih l hl).2 x hx, (ih h hh).2 x hx]
end Groundwork.Sparsify
