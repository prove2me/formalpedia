-- Prove2me | solution 2 for OAI.EntropyRateDimension.FairPairs.geometric_fine_scale_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:31:01.58399+00:00
-- url     : https://prove2.me/submissions/eeeee924-0d30-4629-ae65-ca219836419a

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FairPairs.lean:L393-L413
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FairPairs.geometric_fine_scale_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.MeasureTheory.SelfSimilar.FairPairs ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace FairPairs

theorem geometric_fine_scale_bound (s : Finset ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hs : ∀ h ∈ s, a * (4 : ℝ)^h ≤ 2) :
    (∑ h ∈ s, a * (4 : ℝ)^h) ≤ 8 / 3 := by
  by_cases hn : s.Nonempty
  · let m := s.max' hn
    have hm : m ∈ s := Finset.max'_mem s hn
    have hsub : s ⊆ Finset.range (m + 1) := by
      intro h hh
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' s h hh))
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun h => a * (4 : ℝ)^h) hsub
      (fun h _ _ => mul_nonneg ha (pow_nonneg (by norm_num) h))
    have hg := geom_sum_mul (4 : ℝ) (m + 1)
    have he : (∑ h ∈ Finset.range (m+1), a * (4 : ℝ)^h) * 3 =
        4 * (a * (4 : ℝ)^m) - a := by
      rw [← Finset.mul_sum, mul_assoc]
      norm_num only [show (4 : ℝ) - 1 = 3 by norm_num] at hg
      rw [hg, pow_succ]
      ring
    linarith [hs m hm]
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty]
    norm_num

end FairPairs

end EntropyRateDimension

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FairPairs
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.FairPairs.geometric_fine_scale_bound := @_root_.OAI.EntropyRateDimension.FairPairs.geometric_fine_scale_bound
