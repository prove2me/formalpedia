-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:27:47.768516+00:00
-- url     : https://prove2.me/submissions/e9c3ad27-1384-4890-b527-29c1072f334f

import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.Index
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation

set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]
omit [Fintype R]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (left : X → R) (right : Y → R)
    (f : X → ℂ) (g : Y → ℂ) (j : R) :
    fullCorrelation left right f g j = star (fullCorrelation right left g f (-j)) := by
  classical
  simp only [fullCorrelation, star_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  have heq : left x - right y = j ↔ right y - left x = -j := by
    constructor <;> intro h <;> linear_combination -h
  by_cases h : left x - right y = j
  · simp [h, heq.mp h, star_mul]
  · simp [h, not_congr heq |>.mp h]
end OAI.SevenEighths.CenteredMomentCorrelation
