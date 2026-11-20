-- Prove2me | solution 1 for MeasureTheory.tendsto_zero_of_regular_addContent
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:36:53.164175+00:00
-- url     : https://prove2.me/submissions/a72fc06b-2c4c-424c-8d91-45d25c826362

import Definitions.Def_KolmogorovExtension4_CompactSystem_F000
import Mathlib.MeasureTheory.Measure.AddContent

/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {C R : Set (Set α)} {s : ℕ → Set α}

-- `innerRegular` is defined only for a measure, hence we expand the definition to use it with a
-- content
theorem _root_.solution (hR : IsSetRing R) (m : AddContent ℝ≥0∞ R)
    (hs : ∀ n, s n ∈ R) (hs_anti : Antitone s) (hs_Inter : (⋂ n, s n) = ∅)
    (hC : IsCompactSystem C) (hCR : C ⊆ R)
    (h_reg : ∀ A (_ : A ∈ R) (ε : ℝ≥0∞) (_ : 0 < ε), ∃ K ∈ C, K ⊆ A ∧ m (A \ K) ≤ ε) :
    Filter.Tendsto (fun n ↦ m (s n)) Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  choose K hKC hKs hKm using fun n => h_reg (s n) (hs n) (δ n) (by exact_mod_cast hδpos n)
  have hKi : ⋂ n, K n = ∅ := Set.subset_empty_iff.mp (hs_Inter ▸ Set.iInter_mono hKs)
  obtain ⟨N, hN⟩ := hC K hKC hKi
  have hdm : ∀ i, s i \ K i ∈ R := fun i => hR.sdiff_mem (hs i) (hCR (hKC i))
  refine ⟨N, fun n hn => ?_⟩
  have hsub : s N ⊆ ⋃ i ∈ Finset.range (N+1), (s i \ K i) := by
    intro x hx
    by_contra hc
    simp only [Set.mem_iUnion, Set.mem_sdiff, Finset.mem_range, not_exists, not_and, not_not] at hc
    have : x ∈ Set.dissipate K N := by
      simp only [Set.dissipate, Set.mem_iInter]
      intro i hi
      exact hc i (Nat.lt_succ_of_le hi) (hs_anti hi hx)
    rw [hN] at this
    exact this
  calc m (s n) ≤ m (s N) := addContent_mono hR.isSetSemiring (hs n) (hs N) (hs_anti hn)
    _ ≤ m (⋃ i ∈ Finset.range (N+1), (s i \ K i)) :=
        addContent_mono hR.isSetSemiring (hs N) (hR.biUnion_mem _ (fun i _ => hdm i)) hsub
    _ ≤ ∑ i ∈ Finset.range (N+1), m (s i \ K i) := addContent_biUnion_le hR (fun i _ => hdm i)
    _ ≤ ∑ i ∈ Finset.range (N+1), (δ i : ℝ≥0∞) := Finset.sum_le_sum fun i _ => hKm i
    _ ≤ ∑' i, (δ i : ℝ≥0∞) := ENNReal.sum_le_tsum _
    _ ≤ ε := hδ.le

end MeasureTheory
