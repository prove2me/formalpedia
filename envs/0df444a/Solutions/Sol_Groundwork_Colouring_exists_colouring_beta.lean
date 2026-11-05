-- Prove2me | solution 1 for Groundwork.Colouring.exists_colouring_beta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:01:21.285202+00:00
-- url     : https://prove2.me/submissions/53a90fd5-671b-42c8-91c6-719ba5651cef

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
import Theorems.Thm_Groundwork_Colouring_exists_colouring
import Theorems.Thm_Groundwork_Colouring_le_beta

set_option autoImplicit false
section
open Finset
open Groundwork Groundwork.Colouring
namespace Groundwork.Colouring
theorem _root_.solution {K g : ℕ} (hK : 2 ≤ K) (hg : 3 * K ^ 8 ≤ g)
    (c : Fin g → Fin g → ℕ) (hs : ∀ a b, c a b = c b a) (P : ℕ)
    (hP : ∀ a, ∑ b with b ≠ a, c a b ≤ P) :
    ∃ χ : Fin g → Fin K, (∀ γ, K * #{a | χ a = γ} < 2 * g) ∧
      ∀ γ γ', γ ≠ γ' → ∑ a with χ a = γ, ∑ b with χ b = γ', c a b
        ≤ beta K g (∑ a, ∑ b with b ≠ a, c a b) P := by
  obtain ⟨χ, h1, h2⟩ := exists_colouring hK hg c hs P hP
  exact ⟨χ, h1, fun γ γ' hne => le_beta (by omega) (h2 γ γ' hne)⟩
end Groundwork.Colouring
