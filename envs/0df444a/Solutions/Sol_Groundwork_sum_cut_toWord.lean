-- Prove2me | solution 1 for Groundwork.sum_cut_toWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:45:19.055599+00:00
-- url     : https://prove2.me/submissions/96c9c64e-3fdf-4bae-b1fb-135cc37e85a0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.TakeDrop
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_StepMachines_Prog_Chunks
import Theorems.Thm_Groundwork_sum_toWord
import Theorems.Thm_Groundwork_sum_cut

set_option autoImplicit false
section
open Groundwork
open Finset
variable {ι : Type*} [DecidableEq ι]
namespace Groundwork
theorem _root_.solution {X : Type*} [AddCommMonoid X] [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (e : List ι) (he : e.Nodup) (hP : ∀ i, i ∈ e ↔ P i) (c : ι → ℕ) (d : List Bool)
    (F : (ι → List Bool) → X) :
    ∑ y ∈ range (2 ^ (e.map c).sum), F (cut c d e (toWord (e.map c).sum y))
      = ∑ t ∈ tuples P (fun i => words (c i)) d, F t := by
  rw [sum_toWord _ fun w => F (cut c d e w), sum_cut P e he hP]
end Groundwork
