-- Prove2me | solution 1 for Groundwork.Grid.symm_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:11:29.417816+00:00
-- url     : https://prove2.me/submissions/c39b7e69-d727-4841-9997-5f18932b4ebf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Defs
import Definitions.Def_Groundwork_Net_Net
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Groundwork_Grid_Grid
import Theorems.Thm_Groundwork_Grid_boole_and3
import Theorems.Thm_Groundwork_Grid_prod_ind
import Theorems.Thm_Groundwork_Grid_symm_iff

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {J ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [Fintype α]
namespace Groundwork.Grid
theorem _root_.solution (ℓ : Half ρ γ α) : (if ∀ w w', ℓ w w' = ℓ w' w then (1 : ℤ) else 0) =
    (∏ a, ∏ q ∈ pairs γ, if ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1) then 1 else 0) *
    (∏ i, ∏ p ∈ pairs ρ, if ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i) then 1 else 0) *
    ∏ ω ∈ Ω ρ γ, app Cross.X ℓ ω := by
  have h1 : ∀ a, (∏ q ∈ pairs γ, if ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1) then (1 : ℤ) else 0) =
      if ∀ q ∈ pairs γ, ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1) then 1 else 0 := fun a => prod_ind _ _ Iff.rfl
  have h2 : ∀ i, (∏ p ∈ pairs ρ, if ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i) then (1 : ℤ) else 0) =
      if ∀ p ∈ pairs ρ, ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i) then 1 else 0 := fun i => prod_ind _ _ Iff.rfl
  simp only [h1, h2, app, Cross.X]
  rw [prod_ind univ _ (P := ∀ a, ∀ q ∈ pairs γ, ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1)) (by simp),
    prod_ind univ _ (P := ∀ i, ∀ p ∈ pairs ρ, ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i)) (by simp),
    prod_ind (Ω ρ γ) _ Iff.rfl]
  exact boole_and3 (symm_iff ℓ)
end Groundwork.Grid
