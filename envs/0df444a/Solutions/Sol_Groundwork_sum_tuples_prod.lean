-- Prove2me | solution 1 for Groundwork.sum_tuples_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:31:12.536782+00:00
-- url     : https://prove2.me/submissions/3ca88ed0-f984-46af-963e-8b8aa281d32a

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
theorem _root_.solution [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (T : ι → Finset X') (d : X')
    (H : ι → X' → ℤ) : ∑ t ∈ tuples P T d, ∏ i with P i, H i (t i) = ∏ i with P i, ∑ x ∈ T i, H i x := by
  unfold tuples
  have h := Finset.prod_univ_sum (fun i => if P i then T i else {d}) (fun i x => if P i then H i x else (1 : ℤ))
  simp only [Finset.prod_filter]
  rw [← h]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with hi <;> simp
end Groundwork
