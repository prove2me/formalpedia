-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.grid_support_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:07:10.503246+00:00
-- url     : https://prove2.me/submissions/7bf74b54-49ba-4c25-a9b6-08f4f146771a

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/LocalEntropy.lean:L215-L231
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.grid_support_card_le. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset

-- ---- from OAI.MeasureTheory.SelfSimilar.LocalEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace FiniteEntropy

end FiniteEntropy

namespace MeasureEntropy

theorem grid_support_card_le {B s : ℝ} (hB : 0 ≤ B) (hs : 0 < s) (hs1 : s ≤ 1) :
    ((Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card : ℝ) ≤ (2*B+3)/s := by
  have hf : ⌊-B/s⌋ ≤ ⌊B/s+1⌋ := Int.floor_le_floor (by
    have := div_nonneg hB hs.le
    simp only [neg_div]
    linarith)
  rw [Int.card_Icc, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega : 0 ≤ ⌊B/s+1⌋+1-⌊-B/s⌋)]
  push_cast
  have h1 := Int.floor_le (B/s+1)
  have h2 := Int.lt_floor_add_one (-B/s)
  have h3 : (3 : ℝ) ≤ 3/s := (le_div_iff₀ hs).mpr (by nlinarith)
  calc
    (⌊B/s+1⌋ : ℝ)+1-⌊-B/s⌋ ≤ 2*B/s+3 := by
      simp only [neg_div] at h2 ⊢
      rw [mul_div_assoc]
      linarith
    _ ≤ (2*B+3)/s := by rw [add_div]; linarith

end MeasureEntropy
end EntropyRateDimension

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.grid_support_card_le := @_root_.OAI.EntropyRateDimension.MeasureEntropy.grid_support_card_le
