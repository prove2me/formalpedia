-- Prove2me | solution 1 for Groundwork.SatNet.Consec.succ_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:40:29.173731+00:00
-- url     : https://prove2.me/submissions/bfefe302-7d3f-4a6d-a998-b0417dfad9a2

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
variable {ι V : Type}
variable {idx : ι → ℕ} {lab : ι → Option V}
namespace Groundwork.SatNet
namespace Consec
theorem _root_.solution (hidx : Function.Injective idx) {p q q' : ι}
    (h : Consec idx lab p q) (h' : Consec idx lab p q') : q = q' := by
  obtain ⟨h1, _, h3, h4⟩ := h
  obtain ⟨h1', _, h3', h4'⟩ := h'
  apply hidx
  rcases lt_trichotomy (idx q) (idx q') with hlt | heq | hgt
  · exact absurd h3.symm (h4' q h1 hlt)
  · exact heq
  · exact absurd h3'.symm (h4 q' h1' hgt)
end Consec
end Groundwork.SatNet
