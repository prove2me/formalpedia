-- Prove2me | solution 1 for OAI.EntropyRateDimension.FairPairs.geometric_fine_scale_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:26:56.308135+00:00
-- url     : https://prove2.me/submissions/3ced4db9-d960-4478-b7b8-216611fd257f

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FairPairs
universe uι uα uβ
open scoped BigOperators ENNReal
open MeasureTheory
theorem h44_geo_sum (n : ℕ) : (∑ h ∈ Finset.range (n+1), (4:ℝ)^h) * 3 = 4^(n+1) - 1 := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; ring

theorem solution (s : Finset ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hs : ∀ h ∈ s, a * (4 : ℝ)^h ≤ 2) :
    (∑ h ∈ s, a * (4 : ℝ)^h) ≤ 8 / 3 := by
  rcases s.eq_empty_or_nonempty with hse | hne
  · subst hse; norm_num
  rcases eq_or_lt_of_le ha with h0 | hpos
  · subst h0; simp only [zero_mul, Finset.sum_const_zero]; norm_num
  set H := s.max' hne
  have hsub : s ⊆ Finset.range (H+1) := fun h hh =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (s.le_max' h hh))
  have hH : a * (4:ℝ)^H ≤ 2 := hs H (s.max'_mem hne)
  have h1 : (∑ h ∈ s, a * (4 : ℝ)^h) ≤ ∑ h ∈ Finset.range (H+1), a * (4:ℝ)^h :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at h1
  rw [← Finset.mul_sum]
  have h2 := h44_geo_sum H
  have h3 : (4:ℝ)^(H+1) = 4 * 4^H := by ring
  rw [h3] at h2
  nlinarith

