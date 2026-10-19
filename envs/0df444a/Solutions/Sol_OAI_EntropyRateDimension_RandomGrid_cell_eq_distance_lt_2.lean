-- Prove2me | solution 2 for OAI.EntropyRateDimension.RandomGrid.cell_eq_distance_lt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:42:17.12946+00:00
-- url     : https://prove2.me/submissions/fc450793-ba71-4b20-a65e-e3cf6bbb04a2

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/GridCoupling.lean:L43-L56
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.RandomGrid.cell_eq_distance_lt. The node keeps its source
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

-- ---- from OAI.MeasureTheory.SelfSimilar.GridCoupling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace RandomGrid

attribute [local instance] unitCircleProbability
theorem cell_eq_distance_lt {δ x y : ℝ} (hδ : 0 < δ) (u : AddCircle (1 : ℝ))
    (h : cell δ u x = cell δ u y) : |x-y| < δ := by
  have hx := Int.floor_le (x/δ+shift u)
  have hx' := Int.lt_floor_add_one (x/δ+shift u)
  have hy := Int.floor_le (y/δ+shift u)
  have hy' := Int.lt_floor_add_one (y/δ+shift u)
  change ⌊x/δ+shift u⌋ = ⌊y/δ+shift u⌋ at h
  rw [h] at hx hx'
  have hxy : (x-y)/δ < 1 := by rw [sub_div]; linarith
  have hyx : (y-x)/δ < 1 := by rw [sub_div]; linarith
  have hhxy := (div_lt_iff₀ hδ).mp hxy
  have hhyx := (div_lt_iff₀ hδ).mp hyx
  rw [abs_lt]
  constructor <;> linarith

end RandomGrid

end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.RandomGrid
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] unitCircleProbability


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.RandomGrid.cell_eq_distance_lt := @_root_.OAI.EntropyRateDimension.RandomGrid.cell_eq_distance_lt
