-- Prove2me | solution 1 for Groundwork.SatNet.idx_lt_of_fst_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:17:52.736439+00:00
-- url     : https://prove2.me/submissions/28e97e46-90bc-49cb-acd1-903ce4651266

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Definitions.Def_StepMachines_Math_SatNet

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}
variable [DecidableEq V]
variable {φ : List (List (V × Bool))} {g μ k : ℕ}
namespace Groundwork.SatNet
theorem _root_.solution {p q : Slot g μ k} (h : p.1 < q.1) : idx p < idx q := by
  obtain ⟨a, c, j⟩ := p
  obtain ⟨b, d, i⟩ := q
  have h1 : a.val + 1 ≤ b.val := h
  have h2 := Nat.mul_le_mul_right μ h1
  rw [Nat.succ_mul] at h2
  have h3 : a.val * μ + c.val + 1 ≤ b.val * μ + d.val := by have := c.2; omega
  have h4 := Nat.mul_le_mul_right k h3
  rw [Nat.succ_mul] at h4
  have := j.2
  simp only [idx]
  omega
end Groundwork.SatNet
