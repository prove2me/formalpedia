-- Prove2me | solution 1 for OAI.EntropyRateDimension.MeasureEntropy.grid_support_card_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:00:33.465007+00:00
-- url     : https://prove2.me/submissions/bd9c97e9-7344-45c9-9679-ae8bffa805c9

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uι uα uβ
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution {B s : ℝ} (hB : 0 ≤ B) (hs : 0 < s) (hs1 : s ≤ 1) :
    ((Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card : ℝ) ≤ (2*B+3)/s := by
  rw [Int.card_Icc]
  have hfl1 : (⌊B/s+1⌋ : ℝ) ≤ B/s+1 := Int.floor_le _
  have hfl2 : -B/s - 1 < (⌊-B/s⌋ : ℝ) := by
    have := Int.lt_floor_add_one (-B/s); linarith
  have hBs : 0 ≤ B/s := div_nonneg hB hs.le
  have hle : ⌊-B/s⌋ ≤ ⌊B/s+1⌋ + 1 := by
    have : (⌊-B/s⌋ : ℝ) ≤ ⌊B/s+1⌋ + 1 := by
      have a := Int.floor_le (-B/s)
      have b := Int.lt_floor_add_one (B/s+1)
      have : -B/s = -(B/s) := by ring
      linarith
    exact_mod_cast this
  have hcast : ((⌊B/s+1⌋ + 1 - ⌊-B/s⌋).toNat : ℝ) = ((⌊B/s+1⌋ + 1 - ⌊-B/s⌋ : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rw [hcast]
  push_cast
  have h3 : 3 ≤ 3/s := by rw [le_div_iff₀ hs]; linarith
  have : (2*B+3)/s = 2*(B/s) + 3/s := by field_simp
  rw [this]
  have e : -B/s = -(B/s) := neg_div _ _
  linarith

