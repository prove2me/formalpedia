-- Prove2me | solution 1 for Groundwork.Grid.prod_eq_factorised
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:09:49.535948+00:00
-- url     : https://prove2.me/submissions/1bca057e-a576-4154-a05c-61d224365386

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Grid
import Definitions.Def_Groundwork_Grid_RowNet
import Theorems.Thm_Groundwork_sum_mul_eq


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
namespace Groundwork.Grid
theorem _root_.solution {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β] (x y : ι → β) :
    (∏ i, if x i = y i then (1 : ℤ) else 0) =
      ∑ θ : ι → β, (∏ i, if x i = θ i then 1 else 0) * ∏ i, if y i = θ i then 1 else 0 := by
  simp only [← prod_mul_distrib]
  rw [← Fintype.piFinset_univ]
  exact (prod_congr rfl fun i _ => (sum_mul_eq (fun t => if x i = t then 1 else 0) (y i)).symm).trans
    (Finset.prod_univ_sum (fun _ => univ) fun i t => (if x i = t then (1 : ℤ) else 0) * if y i = t then 1 else 0)
end Groundwork.Grid
