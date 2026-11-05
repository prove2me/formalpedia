-- Prove2me | solution 1 for GraphProblems.stDecideColor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:39:44.075752+00:00
-- url     : https://prove2.me/submissions/2485369f-a63e-4c72-97b6-3c009ab5647e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Blocks
import Definitions.Def_GraphProblems_Color

set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
namespace GraphProblems
theorem _root_.solution : StDecideColor := by
  intro k n G
  have : Finite (G.Coloring (Fin k)) := Finite.of_injective (fun col : G.Coloring (Fin k) => (col : Fin n → Fin k)) DFunLike.coe_injective
  rw [numColorings, Nat.card_ne_zero]
  exact ⟨fun h => ⟨h, this⟩, fun h => h.1⟩
end GraphProblems
