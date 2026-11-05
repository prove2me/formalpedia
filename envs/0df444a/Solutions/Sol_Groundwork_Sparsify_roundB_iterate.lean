-- Prove2me | solution 1 for Groundwork.Sparsify.roundB_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:11:01.416247+00:00
-- url     : https://prove2.me/submissions/3dbdf9f5-4001-451f-aaf7-5ca234908c6c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Function.Iterate
import Definitions.Def_StepMachines_Math_SparsifyTree

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {σ : Type*} (step : σ → Option (σ × σ))
namespace Groundwork.Sparsify
theorem _root_.solution (test : σ → Bool) (i : ℕ) (st out : List σ) :
    (roundB step test)^[i] (st, out.any test) =
      (((round step)^[i] (st, out)).1, ((round step)^[i] (st, out)).2.any test) := by
  induction i generalizing st out with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    obtain _ | ⟨s, r⟩ := st
    · exact ih [] out
    · cases h0 : step s with
      | none =>
        have e1 : roundB step test (s :: r, out.any test) = (r, (s :: out).any test) := by
          simp [roundB, h0]
        have e2 : round step (s :: r, out) = (r, s :: out) := by simp [round, h0]
        rw [e1, e2]; exact ih r (s :: out)
      | some lh =>
        have e1 : roundB step test (s :: r, out.any test) = (lh.1 :: lh.2 :: r, out.any test) := by
          simp [roundB, h0]
        have e2 : round step (s :: r, out) = (lh.1 :: lh.2 :: r, out) := by simp [round, h0]
        rw [e1, e2]; exact ih _ out
end Groundwork.Sparsify
