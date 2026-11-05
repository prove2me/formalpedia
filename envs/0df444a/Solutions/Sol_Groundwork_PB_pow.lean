-- Prove2me | solution 1 for Groundwork.PB.pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:39:48.639559+00:00
-- url     : https://prove2.me/submissions/5559137c-4da7-432a-896c-4f96b894227d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Order.Monotone.Basic
import Definitions.Def_ToTuring_Bound
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul

set_option autoImplicit false
section
section
open Groundwork
open Groundwork.PB
variable {t s : ℕ → ℕ}
namespace Groundwork.PB
theorem _root_.solution (ht : PB t) (k : ℕ) : PB fun n => t n ^ k := by
  induction k with
  | zero => simpa using const 1
  | succ k ih => simpa only [pow_succ] using ih.mul ht
end Groundwork.PB
