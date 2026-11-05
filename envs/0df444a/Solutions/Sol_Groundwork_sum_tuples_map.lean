-- Prove2me | solution 1 for Groundwork.sum_tuples_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:06:31.742319+00:00
-- url     : https://prove2.me/submissions/f059bd89-7419-4066-a9d1-b1cd3c3fc386

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Code
import Mathlib.Data.List.GetD
import Definitions.Def_StepMachines_Math_CodeMore
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_tuples
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
open Groundwork
open Finset
variable {X Y : Type*}
namespace Groundwork
theorem _root_.solution {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M] (P : ι → Prop) [DecidablePred P]
    {T : ι → Finset X} {T' : ι → Finset Y} (d : X) (d' : Y) (φ : ι → Y → X) (h : ∀ i, P i → Set.BijOn (φ i) (T' i) (T i))
    (F : (ι → X) → M) :
    ∑ t ∈ tuples P T d, F t = ∑ t' ∈ tuples P T' d', F fun i => if P i then φ i (t' i) else d := by
  symm
  refine sum_nbij (fun t' i => if P i then φ i (t' i) else d) (fun t' ht' => ?_) (fun t' ht' t'' ht'' e => ?_)
    (fun t ht => ?_) fun _ _ => rfl
  · have ht' := (mem_tuples _ _ _ _).1 ht'
    refine (mem_tuples _ _ _ _).2 fun i => ⟨fun hi => ?_, fun hi => if_neg hi⟩
    rw [if_pos hi]
    exact (h i hi).mapsTo ((ht' i).1 hi)
  · have ht' := (mem_tuples _ _ _ _).1 (mem_coe.1 ht')
    have ht'' := (mem_tuples _ _ _ _).1 (mem_coe.1 ht'')
    funext i
    by_cases hi : P i
    · have e1 := congrFun e i
      simp only [if_pos hi] at e1
      exact (h i hi).injOn ((ht' i).1 hi) ((ht'' i).1 hi) e1
    · rw [(ht' i).2 hi, (ht'' i).2 hi]
  · have ht := (mem_tuples _ _ _ _).1 (mem_coe.1 ht)
    have hex : ∀ i, ∃ y, (P i → y ∈ T' i ∧ φ i y = t i) ∧ (¬P i → y = d') := fun i => by
      by_cases hi : P i
      · obtain ⟨y, hy, e⟩ := (h i hi).surjOn ((ht i).1 hi)
        exact ⟨y, fun _ => ⟨hy, e⟩, fun hn => absurd hi hn⟩
      · exact ⟨d', fun hp => absurd hp hi, fun _ => rfl⟩
    choose y hy using hex
    refine ⟨y, mem_coe.2 ((mem_tuples _ _ _ _).2 fun i => ⟨fun hi => ((hy i).1 hi).1, (hy i).2⟩), funext fun i => ?_⟩
    by_cases hi : P i
    · simp only [if_pos hi]; exact ((hy i).1 hi).2
    · simp only [if_neg hi]; exact ((ht i).2 hi).symm
end Groundwork
