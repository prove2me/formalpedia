-- Prove2me | solution 1 for Groundwork.SatNet.Consec.pred_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:56:17.69725+00:00
-- url     : https://prove2.me/submissions/21530c96-036a-4686-af6b-26b13f065b18

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
theorem _root_.solution (hidx : Function.Injective idx) {p p' q : ι}
    (h : Consec idx lab p q) (h' : Consec idx lab p' q) : p = p' := by
  obtain ⟨h1, _, h3, h4⟩ := h
  obtain ⟨h1', _, h3', h4'⟩ := h'
  apply hidx
  rcases lt_trichotomy (idx p) (idx p') with hlt | heq | hgt
  · exact absurd (h3'.trans h3.symm) (h4 p' hlt h1')
  · exact heq
  · exact absurd (h3.trans h3'.symm) (h4' p hgt h1)
end Consec
end Groundwork.SatNet
