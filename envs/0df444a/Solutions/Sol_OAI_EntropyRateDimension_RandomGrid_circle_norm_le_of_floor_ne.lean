-- Prove2me | solution 1 for OAI.EntropyRateDimension.RandomGrid.circle_norm_le_of_floor_ne
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:46:53.526272+00:00
-- url     : https://prove2.me/submissions/b7a52222-1c37-4b5b-b888-810ade5e4664

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.RandomGrid
universe uα uβ uγ
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] OAI.EntropyRateDimension.RandomGrid.unitCircleProbability


theorem solution {x y : ℝ} (h : ⌊x⌋ ≠ ⌊y⌋) :
    ‖(x : AddCircle (1 : ℝ))‖ ≤ |y - x| := by
  have hn : ‖(x : AddCircle (1 : ℝ))‖ = |x - round x| := by
    rw [AddCircle.norm_eq]; simp
  rw [hn]
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have hlt : ⌊x⌋ < ⌊y⌋ := lt_of_le_of_ne (Int.floor_mono hxy.le) h
    have h1 : x < (⌊y⌋ : ℝ) := by
      have := Int.lt_floor_add_one x
      have : (⌊x⌋ : ℝ) + 1 ≤ ⌊y⌋ := by exact_mod_cast hlt
      linarith
    have h2 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
    refine (round_le x ⌊y⌋).trans ?_
    rw [abs_of_neg (by linarith), abs_of_pos (by linarith)]; linarith
  · exact absurd (congrArg Int.floor hxy) h
  · have hlt : ⌊y⌋ < ⌊x⌋ := lt_of_le_of_ne (Int.floor_mono hxy.le) (Ne.symm h)
    have h1 : y < (⌊x⌋ : ℝ) := by
      have := Int.lt_floor_add_one y
      have : (⌊y⌋ : ℝ) + 1 ≤ ⌊x⌋ := by exact_mod_cast hlt
      linarith
    have h2 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    refine (round_le x ⌊x⌋).trans ?_
    rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith)]; linarith

