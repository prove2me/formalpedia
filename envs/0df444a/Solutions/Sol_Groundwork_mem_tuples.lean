-- Prove2me | solution 1 for Groundwork.mem_tuples
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:23:25.07432+00:00
-- url     : https://prove2.me/submissions/5d6fea4b-5406-4e30-8a1d-8bfac2375c31

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
    (t : ι → X') : t ∈ tuples P T d ↔ ∀ i, (P i → t i ∈ T i) ∧ (¬P i → t i = d) := by
  unfold tuples
  rw [Fintype.mem_piFinset]
  refine forall_congr' fun i => ?_
  split_ifs with h <;> simp [h]
end Groundwork
