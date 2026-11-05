-- Prove2me | solution 1 for Groundwork.Colouring.card_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:04:46.014586+00:00
-- url     : https://prove2.me/submissions/af408104-d26f-47fd-99d4-68cc483644d4

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
import Theorems.Thm_Groundwork_Colouring_card_prescribed

set_option autoImplicit false
section
open Finset
open Groundwork Groundwork.Colouring
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
local notation "K" => Fintype.card κ
local notation "g" => Fintype.card ι
local notation "N" => (Fintype.card κ ^ Fintype.card ι)
namespace Groundwork.Colouring
theorem _root_.solution {a b a' b' : ι} (hab : a ≠ b) (h1 : a ≠ a') (h2 : a ≠ b') (h3 : b ≠ a')
    (h4 : b ≠ b') (h5 : a' ≠ b') (γ γ' : κ) :
    #{χ : ι → κ | (χ a = γ ∧ χ b = γ') ∧ (χ a' = γ ∧ χ b' = γ')} * K ^ 4 = N := by
  have := card_prescribed (κ := κ) {a, b, a', b'} (fun x => if x = a ∨ x = a' then γ else γ')
  have hc : #({a, b, a', b'} : Finset ι) = 4 := by
    rw [card_insert_of_notMem (by simp [hab, h1, h2]), card_insert_of_notMem (by simp [h3, h4]),
      card_pair h5]
  rw [hc] at this
  simpa [hab.symm, h1.symm, h2.symm, h3, h3.symm, h4.symm, h5.symm, and_assoc] using this
end Groundwork.Colouring
