-- Prove2me | solution 1 for Groundwork.sum_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:45:15.405428+00:00
-- url     : https://prove2.me/submissions/99ce57af-0d31-4756-bd6a-bf15c2e289ac

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
import Theorems.Thm_Groundwork_cut_eq_getD
import Theorems.Thm_Groundwork_cut_of_notMem
import Theorems.Thm_Groundwork_sum_cut
import Theorems.Thm_Groundwork_getD_chunks_replicate
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words

set_option autoImplicit false
section
open Groundwork
open Finset
variable {ι : Type*} [DecidableEq ι]
namespace Groundwork
theorem _root_.solution {X : Type*} [AddCommMonoid X] [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (pos : ι → ℕ) (r ℓ : ℕ) (hinj : ∀ i i', P i → P i' → pos i = pos i' → i = i') (hlt : ∀ i, P i → pos i < r)
    (hsurj : ∀ j < r, ∃ i, P i ∧ pos i = j) (d : List Bool) (F : (ι → List Bool) → X) :
    ∑ w ∈ words (r * ℓ), F (fun i => if P i then block ℓ (pos i) w else d)
      = ∑ t ∈ tuples P (fun _ => words ℓ) d, F t := by
  choose inv hinv using hsurj
  let e : List ι := (List.finRange r).map fun j : Fin r => inv j.1 j.2
  have hlen : e.length = r := by simp [e]
  have he : e.Nodup := by
    refine (List.nodup_finRange r).map fun (j j' : Fin r) h => ?_
    have h1 := (hinv j.1 j.2).2
    have h2 := (hinv j'.1 j'.2).2
    change inv j.1 j.2 = inv j'.1 j'.2 at h
    rw [h] at h1
    exact Fin.ext (h1.symm.trans h2)
  have hget : ∀ i (hi : P i), e[pos i]'(by rw [hlen]; exact hlt i hi) = i := by
    intro i hi
    simp only [e, List.getElem_map, List.getElem_finRange]
    exact hinj _ _ (hinv _ _).1 hi (hinv _ _).2
  have hP : ∀ i, i ∈ e ↔ P i := by
    intro i
    constructor
    · intro h
      obtain ⟨j, _, rfl⟩ := List.mem_map.1 h
      exact (hinv j.1 j.2).1
    · intro hi
      rw [← hget i hi]; exact List.getElem_mem _
  have hidx : ∀ i, P i → e.idxOf i = pos i := by
    intro i hi
    have := he.idxOf_getElem (pos i) (by rw [hlen]; exact hlt i hi)
    rwa [hget i hi] at this
  have hmap : e.map (fun _ => ℓ) = List.replicate r ℓ := by rw [List.map_const', hlen]
  have hsum : (e.map fun _ => ℓ).sum = r * ℓ := by rw [hmap]; simp
  rw [← sum_cut P e he hP (fun _ => ℓ) d F, hsum]
  refine sum_congr rfl fun w _ => congrArg F (funext fun i => ?_)
  by_cases hi : P i
  · rw [if_pos hi, cut_eq_getD, hmap, hidx i hi, getD_chunks_replicate _ _ _ _ _ (hlt i hi)]
  · rw [if_neg hi, cut_of_notMem _ _ _ _ fun h => hi ((hP i).1 h)]
end Groundwork
