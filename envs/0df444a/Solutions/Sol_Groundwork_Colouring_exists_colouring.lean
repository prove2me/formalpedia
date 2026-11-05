-- Prove2me | solution 1 for Groundwork.Colouring.exists_colouring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:59:49.326966+00:00
-- url     : https://prove2.me/submissions/7e546f2d-efa7-476d-aa51-5620427baa12

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Floor.Semifield
import Definitions.Def_Groundwork_Net_Colouring
import Theorems.Thm_Groundwork_Colouring_exists_colouring_fintype

set_option autoImplicit false
section
open Finset
open Groundwork Groundwork.Colouring
namespace Groundwork.Colouring
theorem _root_.solution {K g : ℕ} (hK : 2 ≤ K) (hg : 3 * K ^ 8 ≤ g) (c : Fin g → Fin g → ℕ)
    (hs : ∀ a b, c a b = c b a) (P : ℕ) (hP : ∀ a, ∑ b with b ≠ a, c a b ≤ P) :
    ∃ χ : Fin g → Fin K, (∀ γ, K * #{a | χ a = γ} < 2 * g) ∧
      ∀ γ γ', γ ≠ γ' → K ^ 3 * ∑ a with χ a = γ, ∑ b with χ b = γ', c a b
        ≤ K * (∑ a, ∑ b with b ≠ a, c a b) + g * P := by
  have := exists_colouring_fintype (ι := Fin g) (κ := Fin K) c (by simpa using hK)
    (by simpa using hg) hs P hP
  simpa only [Fintype.card_fin] using this
end Groundwork.Colouring
