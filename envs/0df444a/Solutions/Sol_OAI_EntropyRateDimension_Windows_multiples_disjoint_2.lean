-- Prove2me | solution 2 for OAI.EntropyRateDimension.Windows.multiples_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:57:33.885127+00:00
-- url     : https://prove2.me/submissions/29ecf54a-d1e0-492c-bcf9-7e7522aed30b

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/Windows.lean:L31-L43
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Windows.multiples_disjoint. The node keeps its source
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

theorem multiples_disjoint {n j k : ℕ} (hjk : j ≠ k) :
    Disjoint (Finset.Ico (j * n) (j * n + n)) (Finset.Ico (k * n) (k * n + n)) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨hja, haj⟩ := Finset.mem_Ico.mp ha
  obtain ⟨hka, hak⟩ := Finset.mem_Ico.mp hb
  rcases lt_or_gt_of_ne hjk with h | h
  · have hle := Nat.mul_le_mul_right n h
    have : j * n + n ≤ k * n := by simpa [Nat.add_mul] using hle
    omega
  · have hle := Nat.mul_le_mul_right n h
    have : k * n + n ≤ j * n := by simpa [Nat.add_mul] using hle
    omega

end Windows

end EntropyRateDimension

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Windows
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.Windows.multiples_disjoint := @_root_.OAI.EntropyRateDimension.Windows.multiples_disjoint
