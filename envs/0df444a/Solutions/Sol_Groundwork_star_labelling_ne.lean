-- Prove2me | solution 1 for Groundwork.star_labelling_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:45:49.70664+00:00
-- url     : https://prove2.me/submissions/7dfa325e-bb05-4256-b918-f85a29b42980

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Definitions.Def_StepMachines_Prog_Brute

set_option autoImplicit false
section
open Groundwork
open Finset Stepped
namespace Groundwork
theorem _root_.solution (K ℓ : ℕ) (d w : List Bool) {v u : Fin K} (h : u ≠ v) :
    star (labelling K ℓ d w) v u = block ℓ (tri (min v.1 u.1) (max v.1 u.1)) w := by
  have hlt : (pr v u).1 < (pr v u).2 := min_lt_max.2 h.symm
  unfold star labelling
  rw [if_pos hlt]
  rcases le_total v u with h' | h'
  · rw [pr, min_eq_left h', max_eq_right h', min_eq_left (Fin.le_def.1 h'), max_eq_right (Fin.le_def.1 h')]
  · rw [pr, min_eq_right h', max_eq_left h', min_eq_right (Fin.le_def.1 h'), max_eq_left (Fin.le_def.1 h')]
end Groundwork
