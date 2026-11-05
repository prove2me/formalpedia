-- Prove2me | solution 1 for Groundwork.prod_erase_eq_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:45:50.828801+00:00
-- url     : https://prove2.me/submissions/2a4d7c7e-f13f-4dde-91fe-2577070e9dad

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
theorem _root_.solution [Fintype J] [LinearOrder J] (G : J → J → ℤ) :
    ∏ a, ∏ b ∈ univ.erase a, G a b = ∏ p ∈ pairs J, G p.1 p.2 * G p.2 p.1 := by
  rw [← Finset.prod_finset_product' (univ.filter fun p : J × J => p.1 ≠ p.2) univ (fun a => univ.erase a)
    (by intro p; simp [eq_comm])]
  rw [Finset.prod_mul_distrib]
  have h1 : ∏ p ∈ pairs J, G p.2 p.1 = ∏ p ∈ univ.filter (fun p : J × J => p.2 < p.1), G p.1 p.2 :=
    Finset.prod_nbij' Prod.swap Prod.swap (by intro p; simp [pairs]) (by intro p; simp [pairs]) (by intro p; simp)
      (by intro p; simp) (by intro p; simp)
  rw [h1, pairs, ← Finset.prod_union]
  · congr 1; ext p; simp [lt_or_lt_iff_ne]
  · rw [Finset.disjoint_left]; intro p; simp; grind
end Groundwork
