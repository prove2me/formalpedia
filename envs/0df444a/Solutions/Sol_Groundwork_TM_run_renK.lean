-- Prove2me | solution 1 for Groundwork.TM.run_renK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:43:25.77078+00:00
-- url     : https://prove2.me/submissions/b873de71-72d1-4f82-8eab-3bc3d86edfc2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Frag
import Definitions.Def_ToTuring_TM_Rename
import Theorems.Thm_Groundwork_TM_stepAux_renK
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂] {A Λ σ : Type} (φ : K₁ → K₂)
variable {φ}
namespace Groundwork.TM
theorem _root_.solution (hφ : Function.Injective φ) {M : Λ → TM2.Stmt (fun _ : K₁ => A) Λ σ} :
    ∀ {n : ℕ} {l l' : Option Λ} {v v' : σ} {T T' : K₁ → List A}, Run (TM2.step M) ⟨l, v, T⟩ n ⟨l', v', T'⟩ →
      ∀ {S S' : K₂ → List A}, (∀ k, S (φ k) = T k) → (∀ k, S' (φ k) = T' k) → (∀ k, (∀ a, φ a ≠ k) → S' k = S k) →
        Run (TM2.step fun l => renK φ (M l)) ⟨l, v, S⟩ n ⟨l', v', S'⟩
  | 0, _, _, _, _, _, _, h, S, S', hS, hS', ho => by
    cases h
    have : S = S' := by
      funext k
      by_cases hk : ∃ a, φ a = k
      · obtain ⟨a, rfl⟩ := hk; rw [hS, hS']
      · exact (ho k fun a ha => hk ⟨a, ha⟩).symm
    subst this; exact rfl
  | n + 1, none, _, _, _, _, _, ⟨c, hc, _⟩, _, _, _, _, _ => by simp [TM2.step] at hc
  | n + 1, some l, l', v, v', T, T', ⟨c, hc, h⟩, S, S', hS, hS', ho => by
    simp only [TM2.step, Option.some.injEq] at hc
    subst hc
    obtain ⟨h1, h2, h3, h4⟩ := stepAux_renK hφ (M l) v T S hS
    refine ⟨TM2.stepAux (renK φ (M l)) v S, rfl, ?_⟩
    have := solution hφ (S := (TM2.stepAux (renK φ (M l)) v S).stk) (S' := S') h h3 hS'
      fun k hk => (ho k hk).trans (h4 k hk).symm
    rw [← h1, ← h2] at this
    exact this
end Groundwork.TM
