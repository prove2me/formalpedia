-- Prove2me | solution 1 for Groundwork.card_class_pairs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:43:55.51759+00:00
-- url     : https://prove2.me/submissions/1279a1a2-5339-41b7-bb1a-568b524a0e48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net

set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
namespace Groundwork
theorem _root_.solution [Fintype J] [DecidableEq J'] (χ : J → J') {m : ℕ} (hm : ∀ G, #{a | χ a = G} ≤ m)
    (G G' : J') : #{p : J × J | χ p.1 = G ∧ χ p.2 = G'} ≤ m * m := by
  have h : (univ.filter fun p : J × J => χ p.1 = G ∧ χ p.2 = G') =
      (univ.filter fun a => χ a = G) ×ˢ (univ.filter fun b => χ b = G') := by
    ext p; simp
  rw [h, Finset.card_product]
  exact Nat.mul_le_mul (hm G) (hm G')
end Groundwork
