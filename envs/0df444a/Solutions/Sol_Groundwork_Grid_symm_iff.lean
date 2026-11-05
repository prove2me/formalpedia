-- Prove2me | solution 1 for Groundwork.Grid.symm_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:09:35.838521+00:00
-- url     : https://prove2.me/submissions/da96a996-cf59-4f07-960d-69180cae1185

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Defs
import Definitions.Def_Groundwork_Net_Net
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Groundwork_Grid_Grid

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {J ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [Fintype α] [DecidableEq α]
namespace Groundwork.Grid
theorem _root_.solution (ℓ : Half ρ γ α) : (∀ w w', ℓ w w' = ℓ w' w) ↔
    ((∀ a, ∀ q ∈ pairs γ, ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1)) ∧
     (∀ i, ∀ p ∈ pairs ρ, ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i))) ∧
     ∀ ω ∈ Ω ρ γ, ℓ (ω.1.1, ω.2.1) (ω.1.2, ω.2.2) = ℓ (ω.1.2, ω.2.2) (ω.1.1, ω.2.1) ∧
       ℓ (ω.1.1, ω.2.2) (ω.1.2, ω.2.1) = ℓ (ω.1.2, ω.2.1) (ω.1.1, ω.2.2) := by
  constructor
  · intro h
    exact ⟨⟨fun a q _ => h _ _, fun i p _ => h _ _⟩, fun ω _ => ⟨h _ _, h _ _⟩⟩
  · rintro ⟨⟨hr, hc⟩, hd⟩ ⟨a, i⟩ ⟨b, i'⟩
    have hr' : ∀ a i i', i < i' → ℓ (a, i) (a, i') = ℓ (a, i') (a, i) := fun a i i' h =>
      hr a (i, i') (by simp [pairs, h])
    have hc' : ∀ i a b, a < b → ℓ (a, i) (b, i) = ℓ (b, i) (a, i) := fun i a b h =>
      hc i (a, b) (by simp [pairs, h])
    have hd1 : ∀ a b i i', a < b → i < i' → ℓ (a, i) (b, i') = ℓ (b, i') (a, i) := fun a b i i' h h' =>
      (hd ((a, b), (i, i')) (by simp [Ω, h, h'])).1
    have hd2 : ∀ a b i i', a < b → i < i' → ℓ (a, i') (b, i) = ℓ (b, i) (a, i') := fun a b i i' h h' =>
      (hd ((a, b), (i, i')) (by simp [Ω, h, h'])).2
    rcases lt_trichotomy a b with h | h | h <;> rcases lt_trichotomy i i' with h' | h' | h'
    · exact hd1 _ _ _ _ h h'
    · subst h'; exact hc' _ _ _ h
    · exact hd2 _ _ _ _ h h'
    · subst h; exact hr' _ _ _ h'
    · subst h; subst h'; rfl
    · subst h; exact (hr' _ _ _ h').symm
    · exact (hd2 _ _ _ _ h h').symm
    · subst h'; exact (hc' _ _ _ h).symm
    · exact (hd1 _ _ _ _ h h').symm
end Groundwork.Grid
