-- Prove2me | solution 1 for Groundwork.sum_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:43:54.449362+00:00
-- url     : https://prove2.me/submissions/ca2150be-9c13-443d-b9a9-af963a562881

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
theorem _root_.solution [Fintype τ] [DecidableEq τ] (F : τ → ℤ) (z' : τ) :
    ∑ θ, F θ * (if z' = θ then 1 else 0) = F z' := by
  simp
end Groundwork
