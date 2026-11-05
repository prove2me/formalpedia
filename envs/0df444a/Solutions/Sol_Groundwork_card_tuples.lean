-- Prove2me | solution 1 for Groundwork.card_tuples
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:35:22.191428+00:00
-- url     : https://prove2.me/submissions/a7f63796-6a72-48c4-859a-320728359d93

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
theorem _root_.solution [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (T : ι → Finset X') (d : X') :
    #(tuples P T d) = ∏ i with P i, #(T i) := by
  unfold tuples
  rw [Fintype.card_piFinset, Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp
end Groundwork
