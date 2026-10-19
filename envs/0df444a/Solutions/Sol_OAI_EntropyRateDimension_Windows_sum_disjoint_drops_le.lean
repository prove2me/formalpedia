-- Prove2me | solution 1 for OAI.EntropyRateDimension.Windows.sum_disjoint_drops_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:58:23.14412+00:00
-- url     : https://prove2.me/submissions/d8b1c22f-d02a-49a3-85b9-5f58086d634e

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound

open OAI OAI.EntropyRateDimension
universe uα
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution {α : Type uα} (s : Finset α) (u v : α → ℕ)
    (huv : ∀ i ∈ s, u i ≤ v i)
    (hd : (↑s : Set α).PairwiseDisjoint (fun i => Finset.Ico (u i) (v i)))
    (g : ℕ → ℝ) (hg : Antitone g) (hgn : ∀ i, 0 ≤ g i) :
    ∑ i ∈ s, (g (u i) - g (v i)) ≤ g 0 := by
  classical
  set d : ℕ → ℝ := fun m => g m - g (m+1) with hd_def
  have hdn : ∀ m, 0 ≤ d m := fun m => by
    simp only [hd_def]; linarith [hg (Nat.le_succ m)]
  have htel : ∀ a b : ℕ, a ≤ b → g a - g b = ∑ m ∈ Finset.Ico a b, d m := by
    intro a b hab
    rw [Finset.sum_Ico_eq_sub _ hab, Finset.sum_range_sub', Finset.sum_range_sub']
    ring
  have h1 : ∑ i ∈ s, (g (u i) - g (v i)) = ∑ i ∈ s, ∑ m ∈ Finset.Ico (u i) (v i), d m :=
    Finset.sum_congr rfl (fun i hi => htel _ _ (huv i hi))
  rw [h1, ← Finset.sum_biUnion hd]
  set M := s.sup v
  have hsub : s.biUnion (fun i => Finset.Ico (u i) (v i)) ⊆ Finset.range M := by
    intro m hm
    rw [Finset.mem_biUnion] at hm
    obtain ⟨i, hi, hm⟩ := hm
    rw [Finset.mem_Ico] at hm
    rw [Finset.mem_range]
    exact lt_of_lt_of_le hm.2 (Finset.le_sup (f := v) hi)
  calc ∑ m ∈ s.biUnion (fun i => Finset.Ico (u i) (v i)), d m
      ≤ ∑ m ∈ Finset.range M, d m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => hdn m)
    _ = g 0 - g M := Finset.sum_range_sub' _ _
    _ ≤ g 0 := by linarith [hgn M]

