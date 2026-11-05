-- Prove2me | solution 1 for Groundwork.SatNet.Link.used_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:09:39.175946+00:00
-- url     : https://prove2.me/submissions/d07ff452-6955-4bed-9d01-8802dcf2dc5e

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
omit [DecidableEq V]
namespace Groundwork.SatNet
namespace Link
theorem _root_.solution {p q : Slot g μ k} (h : Link φ p q) : lit φ q ≠ none := by
  intro hq; exact h.2.1 (by rw [h.2.2.1]; simp [lab, hq])
end Link
end Groundwork.SatNet
