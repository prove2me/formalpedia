-- Prove2me | solution 2 for OAI.EntropyRateDimension.Windows.sum_disjoint_drops_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:59:20.934037+00:00
-- url     : https://prove2.me/submissions/53122b43-3f75-4f8a-9ca0-623a45c4677f

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/Windows.lean:L45-L70
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Windows.sum_disjoint_drops_le. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound

-- ---- from OAI.MeasureTheory.SelfSimilar.Windows ----
namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace Windows

theorem sum_disjoint_drops_le {α : Type uα} (s : Finset α) (u v : α → ℕ)
    (huv : ∀ i ∈ s, u i ≤ v i)
    (hd : (↑s : Set α).PairwiseDisjoint (fun i => Finset.Ico (u i) (v i)))
    (g : ℕ → ℝ) (hg : Antitone g) (hgn : ∀ i, 0 ≤ g i) :
    ∑ i ∈ s, (g (u i) - g (v i)) ≤ g 0 := by
  classical
  let N := s.sup v
  have htel : ∀ i ∈ s, g (u i) - g (v i) =
      ∑ t ∈ Finset.Ico (u i) (v i), (g t - g (t + 1)) := by
    intro i hi
    have ht := Finset.sum_Ico_sub (fun t => -g t) (huv i hi)
    simpa only [neg_sub_neg] using ht.symm
  simp_rw [Finset.sum_congr rfl htel]
  rw [← Finset.sum_biUnion hd]
  calc
    ∑ t ∈ s.biUnion (fun i => Finset.Ico (u i) (v i)), (g t - g (t + 1)) ≤
        ∑ t ∈ Finset.range N, (g t - g (t + 1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro t ht
        obtain ⟨i, hi, hit⟩ := Finset.mem_biUnion.mp ht
        exact Finset.mem_range.mpr ((Finset.mem_Ico.mp hit).2.trans_le (Finset.le_sup hi))
      · intro t _ _
        exact sub_nonneg.mpr (hg (Nat.le_succ t))
    _ = g 0 - g N := by
      simpa only [neg_sub_neg] using Finset.sum_range_sub (fun t => -g t) N
    _ ≤ g 0 := sub_le_self _ (hgn N)

end Windows

end EntropyRateDimension

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Windows
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uα} : type_of% @_root_.OAI.EntropyRateDimension.Windows.sum_disjoint_drops_le.{uα} := @_root_.OAI.EntropyRateDimension.Windows.sum_disjoint_drops_le.{uα}
