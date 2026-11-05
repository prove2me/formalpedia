-- Prove2me | solution 1 for Groundwork.SatNet.lit_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:56:31.459636+00:00
-- url     : https://prove2.me/submissions/2dc30eb1-3d32-4b68-ac25-00f9e128827d

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
omit [DecidableEq V]
namespace Groundwork.SatNet
theorem _root_.solution {φ : List (List (V × Bool))} {g μ k : ℕ} {p : Slot g μ k} {l : V × Bool}
    (h : lit φ p = some l) : ∃ C ∈ φ, l ∈ C := by
  unfold lit at h
  obtain ⟨C, hC, hl⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨C, List.mem_of_getElem? hC, List.mem_of_getElem? hl⟩
end Groundwork.SatNet
