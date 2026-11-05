-- Prove2me | solution 1 for Groundwork.sum_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:08:48.759772+00:00
-- url     : https://prove2.me/submissions/2555275f-6fec-4e2f-8870-947424fef603

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Groundwork_Cross_Bit
import Theorems.Thm_Groundwork_uncross
import Theorems.Thm_Groundwork_cross_eq_prod

set_option autoImplicit false
section
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution {n : ℕ} (x y u v : Bits n) : ∑ i ∈ range (n + 1), A n i x y u v = cross x y u v := by
  have h : ∀ k, X₁ (x k) (y k) (u k) (v k)
      = -(s (x k) (y k) * s (u k) (v k)) + I₁ (x k) (y k) (u k) (v k) := fun k => by
    rw [uncross]; ring
  rw [cross_eq_prod]
  simp_rw [h]
  rw [prod_add, sum_powerset, card_univ, Fintype.card_fin]
  simp only [A, compl_eq_univ_sdiff]
end Groundwork
