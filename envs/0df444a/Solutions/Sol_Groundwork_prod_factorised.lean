-- Prove2me | solution 1 for Groundwork.prod_factorised
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:03:27.761368+00:00
-- url     : https://prove2.me/submissions/bae93d7f-89c0-4094-aa23-2dea4bba2720

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Function
import Definitions.Def_Groundwork_Net_Calculus
import Theorems.Thm_Groundwork_sum_tuples_prod

set_option autoImplicit false
section
open Groundwork
open Finset
variable {ι X' τ A α : Type*}
namespace Groundwork
theorem _root_.solution [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (T : ι → Finset X') (d : X')
    (f f' : ι → X' → ℤ) :
    ∏ i with P i, ∑ x ∈ T i, f i x * f' i x =
      ∑ t ∈ tuples P T d, (∏ i with P i, f i (t i)) * ∏ i with P i, f' i (t i) := by
  rw [← sum_tuples_prod P T d]
  simp only [Finset.prod_mul_distrib]
end Groundwork
