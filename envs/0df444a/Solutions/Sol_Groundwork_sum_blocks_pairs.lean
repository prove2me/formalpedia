-- Prove2me | solution 1 for Groundwork.sum_blocks_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:46:05.95019+00:00
-- url     : https://prove2.me/submissions/9b25f482-4e7e-4540-84aa-f8cdfd202e0d

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
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_sum_blocks
import Theorems.Thm_Groundwork_tri_lt
import Theorems.Thm_Groundwork_tri_inj
import Theorems.Thm_Groundwork_tri_surj
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words

set_option autoImplicit false
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution {X : Type*} [AddCommMonoid X] (K ℓ : ℕ) (d : List Bool)
    (F : (Fin K × Fin K → List Bool) → X) :
    ∑ w ∈ words (K * (K - 1) / 2 * ℓ), F (fun p => if p.1 < p.2 then block ℓ (tri p.1 p.2) w else d)
      = ∑ t ∈ tuples (fun p : Fin K × Fin K => p.1 < p.2) (fun _ => words ℓ) d, F t := by
  refine sum_blocks (fun p : Fin K × Fin K => p.1 < p.2) (fun p => tri p.1 p.2) _ ℓ ?_ ?_ ?_ d F
  · intro p p' hp hp' h
    obtain ⟨h1, h2⟩ := tri_inj hp hp' h
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  · intro p hp
    exact tri_lt hp p.2.2
  · intro j hj
    obtain ⟨a, b, h1, h2, h3⟩ := tri_surj hj
    exact ⟨(⟨a, by omega⟩, ⟨b, h2⟩), h1, h3⟩
end Groundwork
