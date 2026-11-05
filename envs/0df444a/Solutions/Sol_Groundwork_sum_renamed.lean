-- Prove2me | solution 1 for Groundwork.sum_renamed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:43:53.349887+00:00
-- url     : https://prove2.me/submissions/5e6b0bf7-a256-45f4-85ad-355b5e61371f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Function
import Definitions.Def_Groundwork_Net_Calculus

set_option autoImplicit false
section
open Groundwork
open Finset
variable {ι X' τ A α : Type*}
namespace Groundwork
theorem _root_.solution [Fintype A] [DecidableEq A] (D : Finset A) (dec : A → τ) (Θ : Finset τ)
    (h : Set.BijOn dec D Θ) (f f' : τ → ℤ) :
    ∑ x, (if x ∈ D then f (dec x) else 0) * (if x ∈ D then f' (dec x) else 0) = ∑ θ ∈ Θ, f θ * f' θ := by
  have h1 : ∀ x, (if x ∈ D then f (dec x) else 0) * (if x ∈ D then f' (dec x) else 0) =
      if x ∈ D then f (dec x) * f' (dec x) else 0 := by
    intro x; split_ifs <;> simp
  simp only [h1]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  exact Finset.sum_nbij dec (fun x hx => h.mapsTo hx) h.injOn h.surjOn (fun _ _ => rfl)
end Groundwork
