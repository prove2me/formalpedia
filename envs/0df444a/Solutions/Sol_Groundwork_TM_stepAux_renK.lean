-- Prove2me | solution 1 for Groundwork.TM.stepAux_renK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:42:36.218247+00:00
-- url     : https://prove2.me/submissions/0f80b4fe-b227-44df-a1fb-808282304322

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Frag
import Definitions.Def_ToTuring_TM_Rename
import Theorems.Thm_Groundwork_TM_Run_trans

section
namespace Groundwork.TM
open Turing
variable {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂] {A Λ σ : Type} (φ : K₁ → K₂)
variable {φ} in
/-- Stacks that agree along φ still agree after the same stack was overwritten on both sides. -/
private theorem agree_update (hφ : Function.Injective φ) {T : K₁ → List A} {S : K₂ → List A} (hS : ∀ k, S (φ k) = T k) (k : K₁)
    (w : List A) (k' : K₁) : Function.update S (φ k) w (φ k') = Function.update T k w k' := by
  by_cases h : k' = k
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne (hφ.ne h), hS]
end Groundwork.TM
set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂] {A Λ σ : Type} (φ : K₁ → K₂)
variable {φ}
namespace Groundwork.TM
theorem _root_.solution (hφ : Function.Injective φ) (q : TM2.Stmt (fun _ : K₁ => A) Λ σ) (v : σ) (T : K₁ → List A)
    (S : K₂ → List A) (hS : ∀ k, S (φ k) = T k) :
    (TM2.stepAux (renK φ q) v S).l = (TM2.stepAux q v T).l ∧ (TM2.stepAux (renK φ q) v S).var = (TM2.stepAux q v T).var ∧
      (∀ k, (TM2.stepAux (renK φ q) v S).stk (φ k) = (TM2.stepAux q v T).stk k) ∧
      ∀ k, (∀ a, φ a ≠ k) → (TM2.stepAux (renK φ q) v S).stk k = S k := by
  induction q generalizing v T S with
  | push k f q ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih v _ _ (agree_update hφ hS k (f v :: T k))
    simp only [renK, TM2.stepAux, hS]
    exact ⟨h1, h2, h3, fun k' hk' => (h4 k' hk').trans (Function.update_of_ne (hk' k).symm _ _)⟩
  | peek k f q ih =>
    simp only [renK, TM2.stepAux, hS]
    exact ih _ _ _ hS
  | pop k f q ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih (f v (T k).head?) _ _ (agree_update hφ hS k (T k).tail)
    simp only [renK, TM2.stepAux, hS]
    exact ⟨h1, h2, h3, fun k' hk' => (h4 k' hk').trans (Function.update_of_ne (hk' k).symm _ _)⟩
  | load f q ih => exact ih _ _ _ hS
  | branch p q₁ q₂ ih₁ ih₂ =>
    simp only [renK, TM2.stepAux]
    cases p v
    · exact ih₂ _ _ _ hS
    · exact ih₁ _ _ _ hS
  | goto l => exact ⟨rfl, rfl, hS, fun _ _ => rfl⟩
  | halt => exact ⟨rfl, rfl, hS, fun _ _ => rfl⟩
end Groundwork.TM
