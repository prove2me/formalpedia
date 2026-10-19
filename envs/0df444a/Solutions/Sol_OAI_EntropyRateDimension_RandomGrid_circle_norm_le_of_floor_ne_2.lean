-- Prove2me | solution 2 for OAI.EntropyRateDimension.RandomGrid.circle_norm_le_of_floor_ne
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:21:24.60528+00:00
-- url     : https://prove2.me/submissions/45af9c4d-b2f8-4a4f-9ded-97083fc8a393

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/RandomGrid.lean:L109-L129
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.RandomGrid.circle_norm_le_of_floor_ne. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid

-- ---- from OAI.MeasureTheory.SelfSimilar.RandomGrid ----
namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteDistribution

attribute [local instance] Classical.propDecidable

end FiniteDistribution
namespace RandomGrid

attribute [local instance] OAI.EntropyRateDimension.RandomGrid.unitCircleProbability
theorem circle_norm_le_of_floor_ne {x y : ℝ} (h : ⌊x⌋ ≠ ⌊y⌋) :
    ‖(x : AddCircle (1 : ℝ))‖ ≤ |y - x| := by
  rw [AddCircle.norm_eq]
  simp only [inv_one, one_mul, mul_one]
  rcases lt_or_gt_of_ne h with hxy | hxy
  · apply (round_le x (⌊x⌋ + 1)).trans
    have hy : (⌊x⌋ : ℝ) + 1 ≤ y := by
      have hh : ⌊x⌋ + 1 ≤ ⌊y⌋ := hxy
      have hh' : (⌊x⌋ : ℝ) + 1 ≤ (⌊y⌋ : ℝ) := by exact_mod_cast hh
      exact hh'.trans (Int.floor_le y)
    have hx := Int.lt_floor_add_one x
    rw [Int.cast_add, Int.cast_one, abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · apply (round_le x ⌊x⌋).trans
    have hy : y ≤ (⌊x⌋ : ℝ) := by
      have hh : ⌊y⌋ + 1 ≤ ⌊x⌋ := hxy
      have hh' : (⌊y⌋ : ℝ) + 1 ≤ (⌊x⌋ : ℝ) := by exact_mod_cast hh
      exact (Int.lt_floor_add_one y).le.trans hh'
    have hx := Int.floor_le x
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith

end RandomGrid

namespace MeasureEntropy

end MeasureEntropy

end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.RandomGrid
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] OAI.EntropyRateDimension.RandomGrid.unitCircleProbability


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.RandomGrid.circle_norm_le_of_floor_ne := @_root_.OAI.EntropyRateDimension.RandomGrid.circle_norm_le_of_floor_ne
