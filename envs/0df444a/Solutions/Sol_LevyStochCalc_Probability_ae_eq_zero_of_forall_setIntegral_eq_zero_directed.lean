-- Prove2me | solution 1 for LevyStochCalc.Probability.ae_eq_zero_of_forall_setIntegral_eq_zero_directed
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:21:03.045188+00:00
-- url     : https://prove2.me/submissions/546e7949-7577-4666-9906-5ed3ff79c52a

import Definitions.Def_LevyStochCalc_Probability_SetIntegralPiSystem_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Vanishing set integrals over a π-system

A function that integrates to zero over every set of a π-system integrates to zero over every
set of the σ-algebra that π-system generates, because the sets on which it integrates to zero
form a Dynkin system. If the function is also measurable for that σ-algebra, it vanishes.
-/

open MeasureTheory
open scoped ENNReal

namespace LevyStochCalc.Probability

variable {α : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]



theorem _root_.solution {m m0 : MeasurableSpace α}
    (hm : m ≤ m0) {μ : Measure α} [IsFiniteMeasure μ] {ι : Type*} [Nonempty ι]
    {𝒢 : ι → MeasurableSpace α} (hdir : Directed (· ≤ ·) 𝒢) (hgen : m = ⨆ i, 𝒢 i)
    {f : α → E} (hf : Integrable f μ) (hfm : StronglyMeasurable[m] f)
    (h : ∀ i, ∀ s, MeasurableSet[𝒢 i] s → ∫ x in s, f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  have hS : m = MeasurableSpace.generateFrom (⋃ i, {s | MeasurableSet[𝒢 i] s}) := by
    rw [hgen]; exact (MeasurableSpace.generateFrom_iUnion_measurableSet 𝒢).symm
  have hpi : IsPiSystem (⋃ i, {s | MeasurableSet[𝒢 i] s}) := by
    intro s hs t ht _
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hs ht ⊢
    obtain ⟨i, hi⟩ := hs
    obtain ⟨j, hj⟩ := ht
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, (hik _ hi).inter (hjk _ hj)⟩
  have hint0 : ∫ x, f x ∂μ = 0 := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := h i Set.univ (@MeasurableSet.univ α (𝒢 i))
    rwa [setIntegral_univ] at this
  have hall : ∀ s, MeasurableSet[m] s → ∫ x in s, f x ∂μ = 0 := by
    intro s hs
    refine MeasurableSpace.induction_on_inter (C := fun s _ => ∫ x in s, f x ∂μ = 0) hS hpi
      ?_ ?_ ?_ ?_ s hs
    · simp
    · intro t ht
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at ht
      obtain ⟨i, hi⟩ := ht
      exact h i t hi
    · intro t htm ht
      rw [setIntegral_compl (hm _ htm) hf, ht, hint0, sub_zero]
    · intro g hdisj hgm hg
      rw [integral_iUnion (fun i => hm _ (hgm i)) hdisj hf.integrableOn]
      simp [hg]
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  exact ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_trim hm
    (fun s _ _ => hf.integrableOn) (fun s hs _ => hall s hs)
    (hfm.finStronglyMeasurable (μ.trim hm))

