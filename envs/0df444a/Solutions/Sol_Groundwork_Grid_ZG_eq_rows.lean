-- Prove2me | solution 1 for Groundwork.Grid.ZG_eq_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:09:48.542239+00:00
-- url     : https://prove2.me/submissions/1dd2e525-2609-4b01-98e0-9f104396141b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Grid
import Definitions.Def_Groundwork_Grid_RowNet
import Theorems.Thm_P2M_Groundwork_Grid_prod___rows_436f8d628931


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
namespace Groundwork.Grid
theorem _root_.solution (R : Inst (ρ × γ) α) (G : Rect ρ γ → α → α → α → α → ℤ) :
    ZG R G = ∑ z : ρ → RowSt ρ γ α, (∏ a, rowW R a (z a)) * ∏ p ∈ pairs ρ, rowΨ G p.1 p.2 (z p.1) (z p.2) := by
  unfold ZG
  refine Fintype.sum_equiv (Equiv.curry ρ γ _) _ _ fun ℓ => ?_
  simp only [rowW, rowΨ, Equiv.curry_apply, Function.curry, prod_mul_distrib, Fintype.prod_prod_type, prod_Ω_rows, app,
    Prod.mk.eta]
  rw [Finset.prod_comm (s := univ) (t := pairs ρ)]
  ring
end Groundwork.Grid
