-- Prove2me | solution 1 for Groundwork.sum_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:44:22.197977+00:00
-- url     : https://prove2.me/submissions/be69e1ee-e472-4db4-84f0-d15f7dd61879

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
import Theorems.Thm_Groundwork_cut_of_notMem
import Theorems.Thm_Groundwork_length_cut
import Theorems.Thm_Groundwork_glue_cut
import Theorems.Thm_Groundwork_length_glue
import Theorems.Thm_Groundwork_cut_glue
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words

set_option autoImplicit false
section
open Groundwork
open Finset
variable {ι : Type*} [DecidableEq ι]
namespace Groundwork
theorem _root_.solution {X : Type*} [AddCommMonoid X] [Fintype ι] (P : ι → Prop) [DecidablePred P] (e : List ι)
    (he : e.Nodup) (hP : ∀ i, i ∈ e ↔ P i) (c : ι → ℕ) (d : List Bool) (F : (ι → List Bool) → X) :
    ∑ w ∈ words (e.map c).sum, F (cut c d e w) = ∑ t ∈ tuples P (fun i => words (c i)) d, F t := by
  have hm : ∀ t : ι → List Bool, t ∈ tuples P (fun i => words (c i)) d ↔
      (∀ i ∈ e, (t i).length = c i) ∧ ∀ i, i ∉ e → t i = d := by
    intro t
    simp only [tuples, Fintype.mem_piFinset]
    constructor
    · intro h
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · have := h i; rw [if_pos ((hP i).1 hi)] at this; exact mem_words.1 this
      · have := h i; rw [if_neg (fun hp => hi ((hP i).2 hp))] at this; exact mem_singleton.1 this
    · rintro ⟨h1, h2⟩ i
      by_cases hp : P i
      · rw [if_pos hp]; exact mem_words.2 (h1 i ((hP i).2 hp))
      · rw [if_neg hp]; exact mem_singleton.2 (h2 i fun hi => hp ((hP i).1 hi))
  refine sum_nbij' (cut c d e) (glue e) ?_ ?_ ?_ ?_ fun _ _ => rfl
  · intro w hw
    exact (hm _).2 ⟨fun i hi => length_cut c d e w (mem_words.1 hw) hi, fun i hi => cut_of_notMem c d e w hi⟩
  · intro t ht
    exact mem_words.2 (length_glue c e t ((hm t).1 ht).1)
  · intro w hw
    exact glue_cut c d e he w (mem_words.1 hw)
  · intro t ht
    exact cut_glue c d e he t ((hm t).1 ht).1 ((hm t).1 ht).2
end Groundwork
